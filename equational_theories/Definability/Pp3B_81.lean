import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq348 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq370 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq371 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq375 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq371 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq371 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq371 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq384 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq375
    | (have j0 := eq375 X0 X1
       grind)
    | exact resolve eq375 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq385 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq384 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq450 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq385 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq385
    | exact resolve eq385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq385 x y
       grind)
    | exact superpose eq385 eq16
    | exact resolve eq16 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq517 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq450 X0 (τ X1)
       grind)
    | exact superpose eq450 eq17
    | exact resolve eq17 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq450
  have eq537 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq517
    | exact resolve eq517 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq546 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq537
    | exact resolve eq537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq667 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq461
       have i₂ := eq546 x y
       grind)
    | exact superpose eq546 eq461
    | exact resolve eq461 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq546
  have eq668 : False := by grind
  exact eq668

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxx_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq76 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq80 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq50
    | exact resolve eq50 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq81 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq80
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq80
    | exact resolve eq80 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq90 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq76 sF3
       grind)
    | exact superpose eq76 eq74
    | exact resolve eq74 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq91 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq76 y
       grind)
    | exact superpose eq76 eq90
    | exact resolve eq90 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq90
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq124 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq487 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op (M.op x y) y))) = (M.op (M.op X1 (M.op y (M.op X0 (M.op (M.op x y) y)))) (M.op X0 (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq607 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
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
  have eq767 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq893
    | exact resolve eq893 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq897 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq894
       have r₂ := eq28
       grind)
    | exact resolve eq894 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq899 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq897
    | exact resolve eq897 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq902 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq899 eq65
    | (have r₁ := eq65
       have r₂ := eq899
       grind)
    | exact resolve eq65 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq904 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq899 eq28
    | exact resolve eq28 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq902
  have eq920 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq607 X1 x X3
       have i₂ := eq607 X1 x X0
       grind)
    | exact superpose eq607 eq607
    | exact resolve eq607 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq905 eq105
    | exact resolve eq105 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq905
  have eq960 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq956
  have eq1045 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ (M.op x y)) (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq960 eq14
    | exact resolve eq14 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq960 eq607
    | exact resolve eq607 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq1817 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1049 eq1045
    | exact resolve eq1045 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq1049
  have eq1824 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq2055 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq1824
    | (have j0 := eq1824 (σ x)
       grind)
    | exact resolve eq1824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq2076 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq899 eq2055
    | exact resolve eq2055 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq2083 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2076
  have eq2084 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq2083
    | exact resolve eq2083 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq2193 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq899 eq2084
    | exact resolve eq2084 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq2084
  have eq2200 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2193
  have eq2207 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2200 eq960
    | exact resolve eq960 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq2200
  have eq2221 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2207
  have eq2230 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2221
       have r₂ := eq904
       grind)
    | exact resolve eq2221 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq2221
  have eq2233 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq2230 eq30
    | exact resolve eq30 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2230
  have eq2253 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2233
    | exact resolve eq2233 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233
  have eq2254 : y = (M.op x y) ∨ x = y := by grind
  clear eq2253
  have eq2365 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2254 eq21
    | exact resolve eq21 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2368 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq2254 eq64
    | (have r₁ := eq64
       have r₂ := eq2254
       grind)
    | exact resolve eq64 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2370 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2254 eq124
    | exact resolve eq124 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq2381 : (k y x) = (M.op y y) ∨ x = y := by grind
  clear eq2368
  have eq2391 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2370 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq2370
    | exact resolve eq2370 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2370
  have eq2394 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2365
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2365
    | exact resolve eq2365 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq2605 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq2381
       grind)
    | exact superpose eq2381 eq73
    | exact resolve eq73 eq2381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381
  have eq2610 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2605
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq2605
    | exact resolve eq2605 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2605
  have eq2949 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2610 eq2391
    | exact resolve eq2391 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391 eq2610
  have eq2951 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by grind
  clear eq2949
  have eq6092 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq767 x y
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq767
    | (have j0 := eq767 x y
       grind)
    | exact resolve eq767 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq767
  have eq6123 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6092
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6092
    | exact resolve eq6092 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6092
  have eq6184 : (σ x) = (σ y) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6123
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6123
    | exact resolve eq6123 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6123
  have eq6240 : (σ x) = (σ y) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6184
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6184
    | exact resolve eq6184 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6184
  have eq6287 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6240
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6240
    | exact resolve eq6240 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6240
  have eq6330 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6287
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6287
    | exact resolve eq6287 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6287
  have eq6359 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq6330
    | exact resolve eq6330 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6330
  have eq7339 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq51 eq487
    | exact resolve eq487 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq487
  have eq18154 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2394 eq6359
    | exact resolve eq6359 eq2394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6359
  have eq18166 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq18154
       have r₂ := eq28
       grind)
    | exact resolve eq18154 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18154
  have eq18169 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2951 eq18166
    | exact resolve eq18166 eq2951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951 eq18166
  have eq18172 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq18169
  have eq18310 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op y y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2254 eq7339
    | exact resolve eq7339 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7339
  have eq19784 : y = (M.op (M.op x y) (M.op y (M.op y y))) ∨ x = y := by
    first
    | (have i₁ := eq18310 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18310
    | (have j0 := eq18310 x
       grind)
    | exact resolve eq18310 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18310
  have eq19864 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op X0 y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19784
       have i₂ := eq920 y y X0
       grind)
    | (have i₁ := eq19784
       have i₂ := eq920 X0 y y
       grind)
    | exact superpose eq920 eq19784
    | exact resolve eq19784 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq19784
  have eq20018 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq19864 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19864
    | (have j0 := eq19864 x
       grind)
    | exact resolve eq19864 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19864
  have eq20098 : y = (M.op y (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2254 eq20018
    | exact resolve eq20018 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20018
  have eq20123 : y = (M.op y (M.op x y)) ∨ x = y := by grind
  clear eq20098
  have eq20124 : y = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq20123
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20123
    | exact resolve eq20123 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20123
  have eq20125 : y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2254 eq20124
    | exact resolve eq20124 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20124
  have eq20150 : y = (M.op y y) ∨ x = y := by grind
  clear eq20125
  have eq20242 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq20150
       grind)
    | exact superpose eq20150 eq91
    | exact resolve eq91 eq20150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq20150
  have eq20317 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq20242
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20242
    | exact resolve eq20242 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20242
  have eq20398 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq20317 eq18172
    | exact resolve eq18172 eq20317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18172 eq20317
  have eq20434 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq20398
  have eq20458 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq20434
       have r₂ := eq2394
       grind)
    | exact resolve eq20434 eq2394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394 eq20434
  have eq20558 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20458 eq29
    | exact resolve eq29 eq20458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20458
  have eq20632 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq20558
    | exact resolve eq20558 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq20558
  have eq20666 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq20632 eq2254
    | exact resolve eq2254 eq20632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254 eq20632
  have eq20771 : x = y := by grind
  clear eq20666
  have eq20813 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20771
       grind)
    | exact superpose eq20771 eq19
    | exact resolve eq19 eq20771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20814 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20771
       grind)
    | exact superpose eq20771 eq25
    | exact resolve eq25 eq20771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20771
  have eq20867 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20814
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20814
    | exact resolve eq20814 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20814
  have eq20872 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20867 eq27
    | exact resolve eq27 eq20867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20867
  have eq21021 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20872 eq81
    | exact resolve eq81 eq20872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq20872
  have eq21051 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq21021
       have i₂ := eq20813
       grind)
    | exact superpose eq20813 eq21021
    | exact resolve eq21021 eq20813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20813 eq21021
  have eq21056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21051 eq15
    | exact resolve eq15 eq21051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21051
  have eq21102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq21056
    | exact resolve eq21056 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq21056
  have eq21111 : False := by grind
  exact eq21111

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
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
  have eq83 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq90 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq102 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq102
    | (have j0 := eq102 (σ X0)
       grind)
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq102 x
       grind)
    | exact superpose eq102 eq44
    | (have j1 := eq102 x
       grind)
    | exact resolve eq44 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq399 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
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
  have eq726 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq499 X1 x X0
       grind)
    | exact superpose eq499 eq14
    | exact resolve eq14 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 (M.op X2 X0) X2
       have i₂ := eq499 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq499 eq54
    | exact resolve eq54 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq740 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq735 X0 X1 X2
       have i₂ := eq54 X0 X0 X1
       grind)
    | exact superpose eq54 eq735
    | exact resolve eq735 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq760 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq726 X0 (M.op X0 X0)
       have i₂ := eq726 X0 X0
       grind)
    | exact superpose eq726 eq726
    | exact resolve eq726 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq766 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq726 X0 X1
       grind)
    | exact superpose eq726 eq54
    | exact resolve eq54 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq769 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq766 X1 X0 X2
       have i₂ := eq726 X0 X1
       grind)
    | exact superpose eq726 eq766
    | exact resolve eq766 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq860 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq760 X0
       grind)
    | exact superpose eq760 eq14
    | exact resolve eq14 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1547 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq740 X0 X1 X0
       have i₂ := eq760 X0
       grind)
    | exact superpose eq760 eq740
    | exact resolve eq740 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq760
  have eq3413 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq3480 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 X1 X1
       have i₂ := eq1547 X0 X1
       grind)
    | exact superpose eq1547 eq399
    | exact resolve eq399 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq3481 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3480 X0 x
       have i₂ := eq1547 (M.op X0 X0) x
       grind)
    | exact superpose eq1547 eq3480
    | exact resolve eq3480 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547 eq3480
  have eq3501 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    grind
  have eq3524 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3501 X0
       have i₂ := eq769 X0 X0 X0
       grind)
    | exact superpose eq769 eq3501
    | exact resolve eq3501 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3501
  have eq3545 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3524 (M.op X0 X0)
       have i₂ := eq3481 X0
       grind)
    | exact superpose eq3481 eq3524
    | exact resolve eq3524 eq3481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3481 eq3524
  have eq3559 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3545 X0
       have i₂ := eq769 X0 X0 X0
       grind)
    | exact superpose eq769 eq3545
    | exact resolve eq3545 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq3545
  have eq25215 : y = (M.op y (M.op y (M.op x x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq726 y y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq726
    | exact resolve eq726 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq25231 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25215
       have i₂ := eq860 x y
       grind)
    | exact superpose eq860 eq25215
    | exact resolve eq25215 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25215
  have eq34086 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq25231 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq25231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq34086
    | exact resolve eq34086 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34086
  have eq34098 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq34087
       have r₂ := eq28
       grind)
    | exact resolve eq34087 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34087
  have eq34415 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq34098 eq726
    | exact resolve eq726 eq34098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq34098
  have eq34432 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34415
       have i₂ := eq860 sF2 sF3
       grind)
    | exact superpose eq860 eq34415
    | exact resolve eq34415 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq34415
  have eq34451 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq34432
  have eq34504 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq34451
    | exact resolve eq34451 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34451
  have eq35802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq34504 eq25231
    | exact resolve eq25231 eq34504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25231 eq34504
  have eq35804 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq35802
  have eq35806 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq35804
       have r₂ := eq28
       grind)
    | exact resolve eq35804 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35804
  have eq36073 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq328
       have i₂ := eq35806
       grind)
    | exact superpose eq35806 eq328
    | exact resolve eq328 eq35806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36076 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq35806
  have eq36110 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq36073
  have eq36129 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36076
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36076
    | exact resolve eq36076 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36076
  have eq36130 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36110
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36110
    | exact resolve eq36110 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36110
  have eq37460 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq36129
       grind)
    | exact superpose eq36129 eq70
    | exact resolve eq70 eq36129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq36129
  have eq37478 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq37460
    | exact resolve eq37460 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37460
  have eq37479 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq36130
       have i₂ := eq102 sF2
       grind)
    | exact superpose eq102 eq36130
    | (have j1 := eq102 (σ x)
       grind)
    | exact resolve eq36130 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105486 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq37479
  have eq105550 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq105486
    | exact resolve eq105486 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105486
  have eq107154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq105550 eq37478
    | exact resolve eq37478 eq105550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37478 eq105550
  have eq107161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq107154
  have eq107171 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq107161
       have r₂ := eq28
       grind)
    | exact resolve eq107161 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107161
  have eq107179 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq107560 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq107179 eq36130
    | exact resolve eq36130 eq107179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36130 eq107179
  have eq107575 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq107560
  have eq107580 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq107575 eq107171
    | exact resolve eq107171 eq107575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107171 eq107575
  have eq107628 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq107580
  have eq107658 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq107628 eq30
    | exact resolve eq30 eq107628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq107628
  have eq107855 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq107658
    | exact resolve eq107658 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq107658
  have eq107856 : x = y := by grind
  clear eq107855
  have eq107858 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq107856
       grind)
    | exact superpose eq107856 eq19
    | exact resolve eq19 eq107856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq107859 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq107856
       grind)
    | exact superpose eq107856 eq25
    | exact resolve eq25 eq107856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq107856
  have eq108179 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq107859
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq107859
    | exact resolve eq107859 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107859
  have eq108186 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq108179 eq27
    | exact resolve eq27 eq108179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq108179
  have eq108395 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq328
       have i₂ := eq107858
       grind)
    | exact superpose eq107858 eq328
    | exact resolve eq328 eq107858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq108465 : (M.op x y) = (k x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq3559 x
       have i₂ := eq107858
       grind)
    | exact superpose eq107858 eq3559
    | exact resolve eq3559 eq107858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3559
  have eq108505 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq108395
    | exact resolve eq108395 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108395
  have eq109003 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq119217 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108505 eq102
    | (have j0 := eq102 (σ x)
       grind)
    | exact resolve eq102 eq108505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq119218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108186 eq119217
    | exact resolve eq119217 eq108186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119217
  have eq119232 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq119218
       have r₂ := eq28
       grind)
    | exact resolve eq119218 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119218
  have eq119238 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108186 eq119232
    | exact resolve eq119232 eq108186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119232
  have eq119292 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119238 eq109003
    | exact resolve eq109003 eq119238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109003 eq119238
  have eq119304 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108186 eq119292
    | exact resolve eq119292 eq108186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119292
  have eq119825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119304 eq108505
    | exact resolve eq108505 eq119304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108505 eq119304
  have eq119832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq119825
  have eq119836 : x = (M.op x y) := by
    first
    | (have r₁ := eq119832
       have r₂ := eq28
       grind)
    | exact resolve eq119832 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119832
  have eq119847 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq119836 eq21
    | exact resolve eq21 eq119836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq120219 : x = (k x (M.op x x)) := by
    first
    | exact superpose eq119836 eq108465
    | exact resolve eq108465 eq119836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108465
  have eq120224 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq120219
       have i₂ := eq107858
       grind)
    | exact superpose eq107858 eq120219
    | exact resolve eq120219 eq107858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107858 eq120219
  have eq120402 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq119847
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq119847
    | exact resolve eq119847 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119847
  have eq120404 : x = (k x x) := by
    first
    | exact superpose eq119836 eq120224
    | exact resolve eq120224 eq119836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119836 eq120224
  have eq121862 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3413 x
       have i₂ := eq120404
       grind)
    | exact superpose eq120404 eq3413
    | (have j0 := eq3413 x
       grind)
    | exact resolve eq3413 eq120404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3413 eq120404
  have eq121866 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq121862
  have eq121875 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq121866
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq121866
    | exact resolve eq121866 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq121866
  have eq121892 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108186 eq121875
    | exact resolve eq121875 eq108186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108186 eq121875
  have eq121907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120402 eq121892
    | exact resolve eq121892 eq120402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120402 eq121892
  have eq121920 : False := by grind
  exact eq121920

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_pyy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
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
  clear eq23 eq37
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq351 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
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
  have eq935 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq627 X1 x X3
       have i₂ := eq627 X1 x X0
       grind)
    | exact superpose eq627 eq627
    | exact resolve eq627 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq627 X1 x X0
       grind)
    | exact superpose eq627 eq14
    | exact resolve eq14 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq959 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 (M.op X2 X0) X2
       have i₂ := eq627 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq627 eq54
    | exact resolve eq54 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq966 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq959 X0 X1 X2
       have i₂ := eq54 X0 X0 X1
       grind)
    | exact superpose eq54 eq959
    | exact resolve eq959 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq959
  have eq989 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq948 X0 (M.op X0 X0)
       have i₂ := eq948 X0 X0
       grind)
    | exact superpose eq948 eq948
    | exact resolve eq948 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1098 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq989 X0
       grind)
    | exact superpose eq989 eq14
    | exact resolve eq14 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1630 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq935 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq948 X1 X0
       grind)
    | exact superpose eq948 eq935
    | exact resolve eq935 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq948
  have eq1889 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq966 X0 X1 X0
       have i₂ := eq989 X0
       grind)
    | exact superpose eq989 eq966
    | exact resolve eq966 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq989
  have eq3717 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1 X1
       have i₂ := eq1889 X0 X1
       grind)
    | exact superpose eq1889 eq351
    | exact resolve eq351 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq3718 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3717 X0 x
       have i₂ := eq1889 (M.op X0 X0) x
       grind)
    | exact superpose eq1889 eq3717
    | exact resolve eq3717 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889 eq3717
  have eq3719 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq3718
  have eq24124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24124
    | exact resolve eq24124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24124
  have eq24136 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24125
       have r₂ := eq28
       grind)
    | exact resolve eq24125 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24125
  have eq24150 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq24136 eq1630
    | exact resolve eq1630 eq24136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24136
  have eq24158 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24150 x
       have i₂ := eq1098 sF3 x
       grind)
    | exact superpose eq1098 eq24150
    | exact resolve eq24150 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24150
  have eq24159 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq24158
  have eq24175 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24159 eq3719
    | exact resolve eq3719 eq24159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24159
  have eq24220 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24175
    | exact resolve eq24175 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24175
  have eq24896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24220 eq98
    | exact resolve eq98 eq24220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq24220
  have eq24908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq24896
  have eq24910 : y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24908
       have r₂ := eq28
       grind)
    | exact resolve eq24908 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24908
  have eq24924 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 (M.op y y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1630 x y X0
       have i₂ := eq24910
       grind)
    | exact superpose eq24910 eq1630
    | exact resolve eq1630 eq24910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24910
  have eq24932 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24924 x
       have i₂ := eq1098 y x
       grind)
    | exact superpose eq1098 eq24924
    | exact resolve eq24924 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24924
  have eq24933 : y = (M.op x x) := by grind
  clear eq24932
  have eq24949 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq3719 x
       have i₂ := eq24933
       grind)
    | exact superpose eq24933 eq3719
    | exact resolve eq3719 eq24933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24933
  have eq24994 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq24949
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24949
    | exact resolve eq24949 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24949
  have eq25873 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq24994
       grind)
    | exact superpose eq24994 eq72
    | exact resolve eq72 eq24994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq24994
  have eq25899 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq25873
    | exact resolve eq25873 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25873
  have eq26505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25899 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq25899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq26505
    | exact resolve eq26505 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26505
  have eq26517 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq26506
       have r₂ := eq28
       grind)
    | exact resolve eq26506 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26506
  have eq39362 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq26517 eq1630
    | exact resolve eq1630 eq26517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630 eq26517
  have eq39371 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq39362 x
       have i₂ := eq1098 sF3 x
       grind)
    | exact superpose eq1098 eq39362
    | exact resolve eq39362 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq39362
  have eq39372 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq39371
  have eq39389 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq39372 eq3719
    | exact resolve eq3719 eq39372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719 eq39372
  have eq39437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25899 eq39389
    | exact resolve eq39389 eq25899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25899 eq39389
  have eq39451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq39437
    | exact resolve eq39437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq39437
  have eq39454 : False := by grind
  exact eq39454

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq41 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq42 (τ X0)
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq82
    | exact resolve eq82 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq82
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq140 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq153 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq140
       have i₂ := eq94 y
       grind)
    | exact superpose eq94 eq140
    | exact resolve eq140 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq465 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq464
       have i₂ := eq94 x
       grind)
    | exact superpose eq94 eq464
    | exact resolve eq464 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq465
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq465
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq465 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq465
  have eq503 : (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq502
  have eq548 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 (σ X0) (σ X0) X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq114
    | exact resolve eq114 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1694 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X1 (σ X1)
       have i₂ := eq548 X1 X0
       grind)
    | exact superpose eq548 eq153
    | exact resolve eq153 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq548
  have eq1817 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1694 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1694
    | exact resolve eq1694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1894 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1817 (M.op X0 X0) X0
       have i₂ := eq1817 X0 X0
       grind)
    | exact superpose eq1817 eq1817
    | exact resolve eq1817 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq2018 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq1894 X0
       grind)
    | exact superpose eq1894 eq9
    | exact resolve eq9 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq2193 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2018 (σ X0) X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq2018
    | exact resolve eq2018 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2195 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x x))) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2018 y X0
       have i₂ := eq503
       grind)
    | exact superpose eq503 eq2018
    | exact resolve eq2018 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq2245 : x = y ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2195 x
       have i₂ := eq2018 x x
       grind)
    | exact superpose eq2018 eq2195
    | exact resolve eq2195 eq2018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018 eq2195
  have eq5051 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2245
       grind)
    | exact superpose eq2245 eq16
    | exact resolve eq16 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq5052 : (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5051
       have r₂ := eq94 x
       grind)
    | exact resolve eq5051 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5051
  have eq5054 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq2193 y X0
       have i₂ := eq5052
       grind)
    | exact superpose eq5052 eq2193
    | exact resolve eq2193 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5052
  have eq5102 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5054 x
       have i₂ := eq2193 x x
       grind)
    | exact superpose eq2193 eq5054
    | exact resolve eq5054 eq2193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193 eq5054
  have eq5106 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5102
       grind)
    | exact superpose eq5102 eq10
    | exact resolve eq10 eq5102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5102
  have eq5156 : x = y := by
    first
    | (have i₁ := eq5106
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5106
    | exact resolve eq5106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106
  have eq5330 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5156
       grind)
    | exact superpose eq5156 eq16
    | exact resolve eq16 eq5156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5156
  have eq5331 : False := by grind
  exact eq5331

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 (M.op (M.op X0 X1) X1)) X1) := by
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
  have eq106 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq106 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq106 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq149 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq149 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq149 X0 X1
       grind)
    | exact superpose eq149 eq13
    | (have j0 := eq13 X1 X1
       have j1 := eq149 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq149 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq149 X0 X0
       grind)
    | exact resolve eq13 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq172 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq170 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq170 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq170 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq200 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq524 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X1 X2 X1 X0
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq557 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq524 x X2 X0
       have i₂ := eq524 x X2 X3
       grind)
    | exact superpose eq524 eq524
    | exact resolve eq524 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X2 x
       have i₂ := eq524 x X2 X0
       grind)
    | exact superpose eq524 eq9
    | exact resolve eq9 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 X1 (M.op X0 X1)
       have i₂ := eq524 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq524 eq30
    | exact resolve eq30 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq595 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq582 X0 X1 X2
       have i₂ := eq30 X2 X1 X1
       grind)
    | exact superpose eq30 eq582
    | exact resolve eq582 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq582
  have eq618 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq568 X0 (M.op X0 X0)
       have i₂ := eq568 X0 X0
       grind)
    | exact superpose eq568 eq568
    | exact resolve eq568 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq618 X0
       grind)
    | exact superpose eq618 eq9
    | exact resolve eq9 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq557 X2 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq568 X1 X0
       grind)
    | exact superpose eq568 eq557
    | exact resolve eq557 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq1037 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X1 X1 X0
       have i₂ := eq618 X1
       grind)
    | exact superpose eq618 eq595
    | exact resolve eq595 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq618
  have eq2486 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq893 (M.op X0 X1) X0 X0
       have i₂ := eq893 X1 X0 X0
       grind)
    | exact superpose eq893 eq893
    | exact resolve eq893 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2536 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X2 (M.op X2 X1)))) ≠ (M.op X0 (M.op X0 (M.op X2 (M.op X2 X1)))) ∨ (k X1 X1) = (M.op X0 (M.op X0 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 X0 X0
       have i₂ := eq893 X0 X1 X2
       grind)
    | exact superpose eq893 eq201
    | exact resolve eq201 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq893
  have eq2585 : ∀ X0 X1 X2 : G, (k X1 X1) = (M.op X0 (M.op X0 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2536 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2536
  have eq6769 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X1 X2))) (M.op (M.op X1 (M.op X1 X2)) (M.op X1 (M.op X1 X2)))) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2585 (M.op X0 (M.op X1 (M.op X1 X2))) X2 X1
       have i₂ := eq1037 X0 (M.op X1 (M.op X1 X2))
       grind)
    | exact superpose eq1037 eq2585
    | exact resolve eq2585 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq2585
  have eq6898 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 (M.op X1 X2))) (M.op (M.op X1 (M.op X1 X2)) (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6769 X0 X1 X2
       have i₂ := eq107 X2
       grind)
    | exact superpose eq107 eq6769
    | exact resolve eq6769 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq6769
  have eq7010 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 (M.op X1 X2))) (M.op X1 (M.op (M.op X1 X2) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6898 X0 X1 X2
       have i₂ := eq2486 X1 (M.op X1 X2)
       grind)
    | exact superpose eq2486 eq6898
    | exact resolve eq6898 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6898
  have eq7078 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 (M.op X1 X2))) (M.op X1 (M.op X1 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7010 X0 X1 X2
       have i₂ := eq2486 X1 X2
       grind)
    | exact superpose eq2486 eq7010
    | exact resolve eq7010 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486 eq7010
  have eq7122 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 (M.op X1 X2))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7078 X0 X1 X2
       have i₂ := eq643 X2 X1
       grind)
    | exact superpose eq643 eq7078
    | exact resolve eq7078 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7078
  have eq9524 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X2 (M.op X0 X1))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7122 X0 X0 X1
       have i₂ := eq557 X2 (M.op X0 X1) X0
       grind)
    | (have i₁ := eq7122 X0 X0 X1
       have i₂ := eq557 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq557 eq7122
    | exact resolve eq7122 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq7122
  have eq14038 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X2 (M.op X1 X1))) X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9524 X1 X0 X2
       have i₂ := eq149 X0 X1
       grind)
    | (have i₁ := eq9524 X1 X1 X2
       have i₂ := eq149 X0 X1
       grind)
    | exact superpose eq149 eq9524
    | (have j1 := eq149 X0 X1
       grind)
    | exact resolve eq9524 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq9524
  have eq14382 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14038 X0 X1 x
       have i₂ := eq643 X1 x
       grind)
    | exact superpose eq643 eq14038
    | (have j0 := eq14038 X0 X1 x
       grind)
    | exact resolve eq14038 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq14038
  have eq14448 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14382 X0 X1
       have j1 := eq200 X0 X1
       grind)
    | (have r₁ := eq14382 X0 X1
       have r₂ := eq200 X0 X1
       grind)
    | (have r₁ := eq14382 X1 X1
       have r₂ := eq200 X1 X1
       grind)
    | exact resolve eq14382 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq14382
  have eq14574 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14448 (σ X0) (σ X1)
       grind)
    | exact superpose eq14448 eq15
    | exact resolve eq15 eq14448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14592 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14574 X0 X1
       have i₂ := eq14448 X0 X1
       grind)
    | exact superpose eq14448 eq14574
    | exact resolve eq14574 eq14448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14448 eq14574
  have eq14794 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14592 y x
       grind)
    | exact superpose eq14592 eq16
    | (have r₁ := eq16
       have r₂ := eq14592 y x
       grind)
    | exact resolve eq16 eq14592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14592
  have eq14825 : False := by grind
  exact eq14825

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
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
  have eq303 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
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
  have eq304 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq303 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq362 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq304 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq363 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq362 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq375 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq363 X1 (σ X0)
       grind)
    | exact superpose eq363 eq22
    | (have j1 := eq363 X1 (σ X0)
       grind)
    | exact resolve eq22 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq363 (σ X1) (σ X0)
       grind)
    | exact superpose eq363 eq15
    | (have j1 := eq363 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq363 (τ X1) X0
       grind)
    | exact superpose eq363 eq17
    | (have j1 := eq363 (τ X1) X0
       grind)
    | exact resolve eq17 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq363
  have eq437 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq387
    | exact resolve eq387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq472 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq437 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq437
    | (have j0 := eq437 X0 X1
       grind)
    | exact resolve eq437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq595 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq379 x y
       grind)
    | exact superpose eq379 eq16
    | (have j1 := eq379 x y
       grind)
    | exact resolve eq16 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq620 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq603 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq603
    | (have j0 := eq603 (τ X1) (τ X0)
       grind)
    | exact resolve eq603 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | exact resolve eq620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq630 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq628
    | (have j0 := eq628 X0 X1
       grind)
    | exact resolve eq628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq631 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq630
    | (have j0 := eq630 X0 X1
       grind)
    | exact resolve eq630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq632 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq631 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq631
    | (have j0 := eq631 X0 X1
       grind)
    | exact resolve eq631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq640 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq632 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq632
    | (have j0 := eq632 (τ X0) (τ X1)
       grind)
    | exact resolve eq632 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq632
  have eq687 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq687 X1 x X3
       have i₂ := eq687 X1 x X0
       grind)
    | exact superpose eq687 eq687
    | exact resolve eq687 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq687 X1 x X0
       grind)
    | exact superpose eq687 eq9
    | exact resolve eq9 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (M.op X2 X0) X2
       have i₂ := eq687 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq687 eq62
    | exact resolve eq62 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq738 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq726 X0 X1 X2
       have i₂ := eq62 X0 X0 X1
       grind)
    | exact superpose eq62 eq726
    | exact resolve eq726 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq745 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq718 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq718 X1 X0
       grind)
    | exact superpose eq718 eq718
    | exact resolve eq718 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq718 X0 (M.op X0 X0)
       have i₂ := eq718 X0 X0
       grind)
    | exact superpose eq718 eq718
    | exact resolve eq718 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq718 X0 X1
       grind)
    | exact superpose eq718 eq62
    | exact resolve eq62 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq760 X1 X0 X2
       have i₂ := eq718 X0 X1
       grind)
    | exact superpose eq718 eq760
    | exact resolve eq760 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq773 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1 X0
       have i₂ := eq753 X0
       grind)
    | exact superpose eq753 eq62
    | exact resolve eq62 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq774 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq753 X0
       grind)
    | exact superpose eq753 eq9
    | exact resolve eq9 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq718 X1 (M.op X1 (M.op X0 X0))
       have i₂ := eq774 X0 X1
       grind)
    | exact superpose eq774 eq718
    | exact resolve eq718 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op (σ X1) (M.op X0 X0))) X1) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 (M.op (σ X0) (M.op X0 X0))
       have i₂ := eq774 X0 (σ X0)
       grind)
    | exact superpose eq774 eq375
    | exact resolve eq375 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq831 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X3 X0) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq710 X1 (M.op X2 (M.op (M.op X3 X0) X0)) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq710
    | exact resolve eq710 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq710 X1 (M.op X2 (M.op X0 X0)) X2
       have i₂ := eq774 X0 X2
       grind)
    | exact superpose eq774 eq710
    | exact resolve eq710 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq710 X1 (M.op X2 (M.op X2 X0)) X0
       have i₂ := eq718 X2 X0
       grind)
    | exact superpose eq718 eq710
    | exact resolve eq710 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq837 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq710 X2 (M.op X3 X1) X3
       have i₂ := eq710 X3 X1 X0
       grind)
    | (have i₁ := eq710 X2 (M.op X3 X1) X3
       have i₂ := eq710 X0 X1 X3
       grind)
    | exact superpose eq710 eq710
    | exact resolve eq710 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 X0))) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq738 (M.op X2 (M.op X0 X0)) X2 X1
       have i₂ := eq774 X0 X2
       grind)
    | exact superpose eq774 eq738
    | exact resolve eq738 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq738 (M.op X2 (M.op X2 X0)) X0 X1
       have i₂ := eq718 X2 X0
       grind)
    | exact superpose eq718 eq738
    | exact resolve eq738 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq753 X1
       have i₂ := eq738 X1 X0 X1
       grind)
    | (have i₁ := eq753 X1
       have i₂ := eq738 X1 X1 X0
       grind)
    | exact superpose eq738 eq753
    | exact resolve eq753 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq753
  have eq983 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq916 X0 x X2
       have i₂ := eq955 x (M.op X2 (M.op X2 X0))
       grind)
    | exact superpose eq955 eq916
    | exact resolve eq916 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq984 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X0 X0))) = (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq915 X0 x X2
       have i₂ := eq955 x (M.op X2 (M.op X0 X0))
       grind)
    | exact superpose eq955 eq915
    | exact resolve eq915 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq1002 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq983 X0 X2
       have i₂ := eq718 X2 X0
       grind)
    | exact superpose eq718 eq983
    | exact resolve eq983 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq1040 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq710 X1 X0 (M.op X2 X0)
       have i₂ := eq955 X2 X0
       grind)
    | exact superpose eq955 eq710
    | exact resolve eq710 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1048 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq955 X1 (M.op X0 X0)
       grind)
    | exact superpose eq955 eq774
    | exact resolve eq774 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1061 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq764 (M.op X1 (M.op X0 X0)) X2 X1
       have i₂ := eq774 X0 X1
       grind)
    | exact superpose eq774 eq764
    | exact resolve eq764 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq764 X0 (M.op X2 X0) X1
       have i₂ := eq955 X2 X0
       grind)
    | exact superpose eq955 eq764
    | exact resolve eq764 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1061 X0 X1 x
       have i₂ := eq833 X0 x X1
       grind)
    | exact superpose eq833 eq1061
    | exact resolve eq1061 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq1061
  have eq1316 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq773 X0 X1
       have i₂ := eq1136 X0 X1
       grind)
    | (have i₁ := eq773 X0 X0
       have i₂ := eq1136 X0 X0
       grind)
    | exact superpose eq1136 eq773
    | exact resolve eq773 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq1317 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1
       have i₂ := eq1136 X0 X1
       grind)
    | (have i₁ := eq774 X0 X0
       have i₂ := eq1136 X0 X0
       grind)
    | exact superpose eq1136 eq774
    | exact resolve eq774 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq1367 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq955 X1 (M.op X0 X1)
       have i₂ := eq1136 X1 X0
       grind)
    | (have i₁ := eq955 X1 (M.op X0 X0)
       have i₂ := eq1136 X0 X1
       grind)
    | exact superpose eq1136 eq955
    | exact resolve eq955 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq764 X1 X0 X0
       have i₂ := eq1136 (M.op X0 X1) X0
       grind)
    | exact superpose eq1136 eq764
    | exact resolve eq764 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq1373 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1367 X0 X1
       have i₂ := eq808 X1 X0
       grind)
    | exact superpose eq808 eq1367
    | exact resolve eq1367 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq1367
  have eq1501 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1136 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq1317 X0 X1
       grind)
    | exact superpose eq1317 eq1136
    | exact resolve eq1136 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1504 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1501 X0 X1
       have i₂ := eq1373 X0 (M.op X1 X0)
       grind)
    | exact superpose eq1373 eq1501
    | exact resolve eq1501 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1521 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1504 X0 X1
       have i₂ := eq1373 X1 X0
       grind)
    | exact superpose eq1373 eq1504
    | exact resolve eq1504 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1528 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1521 X0 X1
       have i₂ := eq1316 X0 X1
       grind)
    | exact superpose eq1316 eq1521
    | exact resolve eq1521 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq1521
  have eq2364 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) = (M.op X3 (M.op X3 (M.op X0 (M.op (M.op X1 X2) X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq834 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) X3 x
       have i₂ := eq61 X2 x X0 X1
       grind)
    | exact superpose eq61 eq834
    | exact resolve eq834 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq2378 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq834 X2 X1 X1
       have i₂ := eq710 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq834 X2 X1 X1
       have i₂ := eq710 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq710 eq834
    | exact resolve eq834 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2473 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X1 (M.op X2 (M.op X2 X0)))) = (M.op (M.op X0 X0) (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq955 X1 (M.op X1 (M.op X2 (M.op X2 X0)))
       have i₂ := eq834 X0 X1 X2
       grind)
    | exact superpose eq834 eq955
    | exact resolve eq955 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2488 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 (M.op X2 X0)))) = (M.op X1 (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2473 X0 X1 X2
       have i₂ := eq1373 X1 (M.op X2 (M.op X2 X0))
       grind)
    | exact superpose eq1373 eq2473
    | exact resolve eq2473 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq2546 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2364 X0 X1 X2 x
       have i₂ := eq831 X2 x X0 X1
       grind)
    | exact superpose eq831 eq2364
    | exact resolve eq2364 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq2364
  have eq2573 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2488 X0 X1 X2
       have i₂ := eq1002 X0 X2
       grind)
    | exact superpose eq1002 eq2488
    | exact resolve eq2488 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq2594 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X0 (M.op (M.op X1 X2) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2546 X0 X1 X2
       have i₂ := eq1373 X2 (M.op X0 (M.op (M.op X1 X2) X2))
       grind)
    | exact superpose eq1373 eq2546
    | exact resolve eq2546 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546
  have eq2613 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X2 (M.op X0 (M.op (M.op (M.op X1 X2) X2) (M.op (M.op X1 X2) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2594 X0 X1 X2
       have i₂ := eq1373 X0 (M.op (M.op X1 X2) X2)
       grind)
    | exact superpose eq1373 eq2594
    | exact resolve eq2594 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq2618 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2613 X0 X1 X2
       have i₂ := eq1373 (M.op X1 X2) X2
       grind)
    | exact superpose eq1373 eq2613
    | exact resolve eq2613 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613
  have eq2619 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X2 (M.op X0 (M.op X2 (M.op (M.op X1 X2) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2618 X0 X1 X2
       have i₂ := eq1136 X2 (M.op X1 X2)
       grind)
    | exact superpose eq1136 eq2618
    | exact resolve eq2618 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136 eq2618
  have eq2620 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op X2 (M.op X0 (M.op X2 (M.op X2 X2)))) := by
    intro X0 X2
    first
    | (have i₁ := eq2619 X0 x X2
       have i₂ := eq955 x X2
       grind)
    | exact superpose eq955 eq2619
    | exact resolve eq2619 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq3270 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2378 X2 X1 (M.op X0 (M.op X1 X0))
       have i₂ := eq1317 X0 X1
       grind)
    | exact superpose eq1317 eq2378
    | exact resolve eq2378 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq3297 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2378 X0 (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))
       have i₂ := eq1002 X0 X2
       grind)
    | exact superpose eq1002 eq2378
    | exact resolve eq2378 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq3392 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 (M.op X1 (M.op X0 (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1369 X2 X3
       have i₂ := eq2378 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq2378 eq1369
    | exact resolve eq1369 eq2378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3537 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3270 X0 X1 X2
       have i₂ := eq1373 X0 (M.op X1 X0)
       grind)
    | exact superpose eq1373 eq3270
    | exact resolve eq3270 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3270
  have eq3585 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3537 X0 X1 X2
       have i₂ := eq1373 X1 X0
       grind)
    | exact superpose eq1373 eq3537
    | exact resolve eq3537 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537
  have eq3621 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = (M.op (M.op X2 (M.op X2 X0)) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2620 X1 (M.op X2 (M.op X2 X0))
       have i₂ := eq834 X0 (M.op X2 (M.op X2 X0)) X2
       grind)
    | exact superpose eq834 eq2620
    | exact resolve eq2620 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3624 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2620 X2 X1
       have i₂ := eq710 X1 X1 X0
       grind)
    | (have i₁ := eq2620 X2 X1
       have i₂ := eq710 X0 X1 X1
       grind)
    | exact superpose eq710 eq2620
    | exact resolve eq2620 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq2620
  have eq9858 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1528 (M.op X2 (M.op X2 X0)) X1
       have i₂ := eq3297 X0 X2 X2
       grind)
    | exact superpose eq3297 eq1528
    | exact resolve eq1528 eq3297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq11872 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X2 (M.op X2 X0)) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1369 X2 (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0))
       have i₂ := eq9858 X0 X1 X2
       grind)
    | exact superpose eq9858 eq1369
    | exact resolve eq1369 eq9858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq49457 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X2))) ≠ X2 ∨ (M.op (M.op X0 (M.op X2 X2)) (M.op X0 (M.op X2 X2))) = (k (M.op X0 (M.op X2 X2)) X2) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq3585 X2 X0 X1
       grind)
    | (have i₁ := eq13 (M.op X2 (M.op X2 X0)) X1
       have i₂ := eq3585 X0 X1 X2
       grind)
    | exact superpose eq3585 eq13
    | (have j0 := eq13 (M.op X0 (M.op X2 X2)) X2
       grind)
    | exact resolve eq13 eq3585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585
  have eq50150 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X2 X2))) = (k (M.op X0 (M.op X2 X2)) X2) ∨ (M.op X0 (M.op X1 (M.op X1 X2))) ≠ X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49457 X0 X1 X2
       have i₂ := eq984 X2 X0
       grind)
    | exact superpose eq984 eq49457
    | (have j0 := eq49457 X0 X1 X2
       grind)
    | exact resolve eq49457 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49457
  have eq50575 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X2 X2))) = (k (M.op X0 (M.op X2 X2)) X2) ∨ (M.op X0 (M.op X1 (M.op X1 X2))) ≠ X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq50150 X0 X1 X2
       have j1 := eq12 (M.op X0 (M.op X2 X2)) X2
       grind)
    | (have r₁ := eq50150 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq50150 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50150
  have eq61159 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ (M.op (σ (τ X1)) (M.op X0 X0)))) X1) ∨ (σ (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ (M.op (σ (τ X1)) (M.op X0 X0)))
       have i₂ := eq809 X0 (τ X1)
       grind)
    | exact superpose eq809 eq18
    | (have j1 := eq809 (k (σ (τ (M.op (σ (τ X1)) (M.op X0 X0)))) X1) (τ X0)
       grind)
    | exact resolve eq18 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq809
  have eq61163 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op (σ (τ X1)) (M.op X0 X0)) X1) ∨ (σ (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61159 X0 X1
       have i₂ := eq11 (M.op (σ (τ X1)) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq61159
    | (have j0 := eq61159 (k (M.op (σ (τ X1)) (M.op X0 X0)) X1) X0
       grind)
    | exact resolve eq61159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61159
  have eq61191 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op X1 (M.op X0 X0)) X1) ∨ (σ (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61163 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq61163
    | (have j0 := eq61163 (k (M.op X1 (M.op X0 X0)) X1) X0
       grind)
    | exact resolve eq61163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61163
  have eq61201 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 X0)) X1) = X0 ∨ (σ (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61191 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61191
    | (have j0 := eq61191 X0 X1
       grind)
    | exact resolve eq61191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61191
  have eq61206 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 X0)) X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61201 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq61201
    | (have j0 := eq61201 X0 X1
       grind)
    | exact resolve eq61201 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61201
  have eq61254 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61206 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq1085 X0 X1 X0
       grind)
    | exact superpose eq1085 eq61206
    | (have j0 := eq61206 (M.op X0 X0) (k X0 (M.op X1 X0))
       grind)
    | exact resolve eq61206 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq61206
  have eq63797 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0))) = (k (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0)) X0) ∨ (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61254 (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0)) X2
       have i₂ := eq9858 X0 X1 X2
       grind)
    | exact superpose eq9858 eq61254
    | exact resolve eq61254 eq9858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9858 eq61254
  have eq63890 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))) = (k (M.op X2 (M.op X0 X0)) X0) ∨ (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63797 X0 X2 X1
       have i₂ := eq11872 X0 X1 X2
       grind)
    | exact superpose eq11872 eq63797
    | (have j0 := eq63797 X0 X1 X2
       grind)
    | exact resolve eq63797 eq11872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11872 eq63797
  have eq63940 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 X0))) = (k (M.op X2 (M.op X0 X0)) X0) ∨ (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63890 X0 X1 X2
       have i₂ := eq984 X0 X2
       grind)
    | exact superpose eq984 eq63890
    | (have j0 := eq63890 X0 X1 X2
       grind)
    | exact resolve eq63890 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984 eq63890
  have eq63988 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X2 X0) (M.op X2 X0))) = X0 ∨ (M.op X0 (M.op X2 (M.op X0 X0))) = (k (M.op X2 (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63940 X0 X1 X2
       have i₂ := eq1373 (M.op X1 (M.op X1 X0)) (M.op X2 X0)
       grind)
    | exact superpose eq1373 eq63940
    | (have j0 := eq63940 X0 X1 X2
       grind)
    | exact resolve eq63940 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63940
  have eq64017 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X2 (M.op X0 X0))) = X0 ∨ (M.op X0 (M.op X2 (M.op X0 X0))) = (k (M.op X2 (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63988 X0 X1 X2
       have i₂ := eq1373 X2 X0
       grind)
    | exact superpose eq1373 eq63988
    | (have j0 := eq63988 X0 X1 X2
       grind)
    | exact resolve eq63988 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373 eq63988
  have eq64043 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 (M.op X1 X0))) = X0 ∨ (M.op X0 (M.op X2 (M.op X0 X0))) = (k (M.op X2 (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64017 X0 X1 X2
       have i₂ := eq3621 X0 X2 X1
       grind)
    | exact superpose eq3621 eq64017
    | (have j0 := eq64017 X0 X1 X2
       grind)
    | exact resolve eq64017 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621 eq64017
  have eq64061 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X0 X0))) = (k (M.op X2 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have j0 := eq64043 X0 x X2
       have j1 := eq50575 X2 x X0
       grind)
    | (have r₁ := eq64043 X2 x X0
       have r₂ := eq50575 X0 x X2
       grind)
    | exact resolve eq64043 eq50575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50575 eq64043
  have eq64119 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 (M.op X0 X1)))) = (k (M.op X2 (M.op X0 (M.op X0 X1))) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64061 (M.op X0 X0) X2
       have i₂ := eq1040 X0 X1 X0
       grind)
    | exact superpose eq1040 eq64061
    | exact resolve eq64061 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq64155 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64061 (M.op X0 X0) (M.op x (M.op X0 X0))
       have i₂ := eq1048 X0 x
       grind)
    | exact superpose eq1048 eq64061
    | exact resolve eq64061 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq64167 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (k (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64061 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq745 X0 X1
       grind)
    | exact superpose eq745 eq64061
    | exact resolve eq64061 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq64061
  have eq64211 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64167 X0 X1
       have i₂ := eq718 X0 X1
       grind)
    | exact superpose eq718 eq64167
    | exact resolve eq64167 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64167
  have eq64217 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64155 X0
       have i₂ := eq955 X0 X0
       grind)
    | exact superpose eq955 eq64155
    | exact resolve eq64155 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64155
  have eq64249 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k (M.op X2 (M.op X0 (M.op X0 X1))) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64119 X0 X1 X2
       have i₂ := eq2573 X1 X2 X0
       grind)
    | exact superpose eq2573 eq64119
    | exact resolve eq64119 eq2573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573 eq64119
  have eq64519 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (M.op X1 (σ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 (M.op X1 (σ X0))) X0
       have i₂ := eq64211 X1 (σ X0)
       grind)
    | exact superpose eq64211 eq22
    | exact resolve eq22 eq64211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64211
  have eq64538 : ∀ X0 X1 : G, (k (τ (M.op X1 (M.op X1 (σ X0)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64519 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64519
    | exact resolve eq64519 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64519
  have eq64779 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq640 X0 (M.op X0 X0)
       have i₂ := eq64217 X0
       grind)
    | exact superpose eq64217 eq640
    | (have j0 := eq640 X0 (M.op X0 X0)
       grind)
    | exact resolve eq640 eq64217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq64217
  have eq64790 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq64779 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64779
  have eq67354 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X1 (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2378 X1 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq64790 X0
       grind)
    | exact superpose eq64790 eq2378
    | exact resolve eq2378 eq64790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378 eq64790
  have eq67432 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67354 X0 x
       have i₂ := eq718 x (τ (M.op X0 X0))
       grind)
    | exact superpose eq718 eq67354
    | exact resolve eq67354 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67354
  have eq67578 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq67432 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq67432
    | exact resolve eq67432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67432
  have eq67913 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op X0 (M.op X0 (M.op X1 (M.op X1 (σ X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67578 X2
       have i₂ := eq834 (σ X2) X0 X1
       grind)
    | exact superpose eq834 eq67578
    | exact resolve eq67578 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq67920 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq67578 X0
       grind)
    | exact superpose eq67578 eq11
    | exact resolve eq11 eq67578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67578
  have eq67988 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ (M.op X0 X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64538 X0 (σ X0)
       have i₂ := eq67920 X0
       grind)
    | exact superpose eq67920 eq64538
    | exact resolve eq64538 eq67920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64538
  have eq121517 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = (k (M.op X1 (M.op X0 X0)) (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64249 X0 (M.op X2 (M.op X2 X0)) X1
       have i₂ := eq3624 X2 X0 X0
       grind)
    | exact superpose eq3624 eq64249
    | exact resolve eq64249 eq3624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3624
  have eq121586 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = (k X0 (M.op (M.op X2 (M.op X2 (M.op X1 X0))) (M.op X2 (M.op X2 (M.op X1 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64249 X2 (M.op X2 (M.op X2 (M.op X1 X0))) X1
       have i₂ := eq3392 X2 X2 X1 X0
       grind)
    | exact superpose eq3392 eq64249
    | exact resolve eq64249 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392 eq64249
  have eq121772 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X0)) = (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121586 X0 X1 X2
       have i₂ := eq3297 (M.op X1 X0) X2 X2
       grind)
    | exact superpose eq3297 eq121586
    | exact resolve eq121586 eq3297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121586
  have eq121825 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = (k (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121517 X0 X1 X2
       have i₂ := eq3297 X0 X2 X2
       grind)
    | exact superpose eq3297 eq121517
    | exact resolve eq121517 eq3297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3297 eq121517
  have eq137346 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (k (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq837 x X1 X2 X0
       have i₂ := eq121825 X1 X0 x
       grind)
    | exact superpose eq121825 eq837
    | exact resolve eq837 eq121825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq121825
  have eq169446 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 (M.op (σ X2) (σ X2)))) X2) = (τ (M.op X0 (M.op X0 (M.op X1 (σ X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op X1 (M.op (σ X2) (σ X2))) X2
       have i₂ := eq137346 X1 (σ X2) X0
       grind)
    | exact superpose eq137346 eq22
    | exact resolve eq22 eq137346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq137346
  have eq169453 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 (M.op X1 (σ X2))))) = (k (τ (M.op X1 (σ (M.op X2 X2)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169446 X0 X1 X2
       have i₂ := eq67920 X2
       grind)
    | exact superpose eq67920 eq169446
    | exact resolve eq169446 eq67920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67920 eq169446
  have eq540182 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq595
       have i₂ := eq472 y x
       grind)
    | exact superpose eq472 eq595
    | (have j1 := eq472 (σ y) (σ x)
       grind)
    | (have r₁ := eq595
       have r₂ := eq472 y x
       grind)
    | exact resolve eq595 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq595
  have eq540183 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq540182
  have eq540207 : ∀ X0 : G, (M.op y y) = (τ (M.op X0 (M.op X0 (M.op (σ x) (σ x))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq67913 X0 (σ x) y
       have i₂ := eq540183
       grind)
    | exact superpose eq540183 eq67913
    | exact resolve eq67913 eq540183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67913 eq540183
  have eq540677 : (M.op y y) = (k (τ (M.op (σ x) (σ (M.op x x)))) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq540207 x
       have i₂ := eq169453 x (σ x) x
       grind)
    | exact superpose eq169453 eq540207
    | exact resolve eq540207 eq169453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169453 eq540207
  have eq540830 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq540677
       have i₂ := eq67988 x
       grind)
    | exact superpose eq67988 eq540677
    | exact resolve eq540677 eq67988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67988 eq540677
  have eq541145 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq955 y y
       have i₂ := eq540830
       grind)
    | exact superpose eq540830 eq955
    | exact resolve eq955 eq540830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq540830
  have eq541332 : x = (M.op x y) := by grind
  clear eq541145
  have eq541600 : ∀ X0 : G, (k y x) = (M.op x (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq121772 y x x
       have i₂ := eq541332
       grind)
    | exact superpose eq541332 eq121772
    | exact resolve eq121772 eq541332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121772
  have eq541631 : x = (k y x) := by
    first
    | (have i₁ := eq541600 x
       have i₂ := eq718 x x
       grind)
    | exact superpose eq718 eq541600
    | exact resolve eq541600 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq541600
  have eq541903 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq603 x y
       have i₂ := eq541631
       grind)
    | exact superpose eq541631 eq603
    | (have j0 := eq603 x y
       grind)
    | exact resolve eq603 eq541631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq541631
  have eq541912 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq541903
  have eq554274 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq541912
       grind)
    | exact superpose eq541912 eq16
    | exact resolve eq16 eq541912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541912
  have eq554800 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq554274
       have i₂ := eq541332
       grind)
    | exact superpose eq541332 eq554274
    | exact resolve eq554274 eq541332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541332 eq554274
  have eq554801 : False := by grind
  exact eq554801

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
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
  have eq275 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
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
  have eq276 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq278 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq275 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq283 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq277 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq277 X0
       grind)
    | exact resolve eq12 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq284 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq305 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq284 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq306 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq305 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq353 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq306 (σ X0)
       grind)
    | exact superpose eq306 eq15
    | exact resolve eq15 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq353 X0
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq353
    | exact resolve eq353 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq353
  have eq641 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq278 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq642 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq641 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq657 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq642 (σ X1) (σ X0)
       grind)
    | exact superpose eq642 eq15
    | (have j1 := eq642 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq642 (τ X1) X0
       grind)
    | exact superpose eq642 eq17
    | (have j1 := eq642 (τ X1) X0
       grind)
    | exact resolve eq17 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq642
  have eq736 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq665
    | exact resolve eq665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq787 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq736
    | (have j0 := eq736 X0 X1
       grind)
    | exact resolve eq736 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq996 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq657 x y
       grind)
    | exact superpose eq657 eq16
    | (have j1 := eq657 x y
       grind)
    | exact resolve eq16 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq1141 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq996
       have i₂ := eq787 y x
       grind)
    | exact superpose eq787 eq996
    | (have j1 := eq787 (σ y) (σ x)
       grind)
    | (have r₁ := eq996
       have r₂ := eq787 y x
       grind)
    | exact resolve eq996 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq996
  have eq1142 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1141
  have eq6989 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq7056 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6989 X1 x X3
       have i₂ := eq6989 X1 x X0
       grind)
    | exact superpose eq6989 eq6989
    | exact resolve eq6989 eq6989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7080 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq6989 X1 x X0
       grind)
    | exact superpose eq6989 eq9
    | exact resolve eq9 eq6989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7107 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 (M.op X2 X0) X2
       have i₂ := eq6989 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq6989 eq24
    | exact resolve eq24 eq6989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6989
  have eq7133 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7107 X0 X1 X2
       have i₂ := eq24 X0 X0 X1
       grind)
    | exact superpose eq24 eq7107
    | exact resolve eq7107 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7107
  have eq7188 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq7080 X0 (M.op X0 X0)
       have i₂ := eq7080 X0 X0
       grind)
    | exact superpose eq7080 eq7080
    | exact resolve eq7080 eq7080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7224 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7188 (σ X0)
       have i₂ := eq372 X0
       grind)
    | exact superpose eq372 eq7188
    | exact resolve eq7188 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7230 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq7188 X0
       grind)
    | exact superpose eq7188 eq9
    | exact resolve eq9 eq7188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7421 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7056 X1 (M.op X2 (M.op X2 X0)) X0
       have i₂ := eq7080 X2 X0
       grind)
    | exact superpose eq7080 eq7056
    | exact resolve eq7056 eq7080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7703 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7188 X1
       have i₂ := eq7133 X1 X0 X1
       grind)
    | (have i₁ := eq7188 X1
       have i₂ := eq7133 X1 X1 X0
       grind)
    | exact superpose eq7133 eq7188
    | exact resolve eq7188 eq7133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7133 eq7188
  have eq13574 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7421 y X0 x
       have i₂ := eq1142
       grind)
    | exact superpose eq1142 eq7421
    | exact resolve eq7421 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq13603 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7421 X2 X1 X1
       have i₂ := eq7056 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq7421 X2 X1 X1
       have i₂ := eq7056 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq7056 eq7421
    | exact resolve eq7421 eq7056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7056 eq7421
  have eq13909 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13574 x
       have i₂ := eq7230 x x
       grind)
    | exact superpose eq7230 eq13574
    | exact resolve eq13574 eq7230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7230 eq13574
  have eq20004 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13603 X0 (σ x) (σ y)
       have i₂ := eq13909
       grind)
    | exact superpose eq13909 eq13603
    | exact resolve eq13603 eq13909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13603 eq13909
  have eq20006 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq20004 x
       have i₂ := eq7080 x (σ x)
       grind)
    | exact superpose eq7080 eq20004
    | exact resolve eq20004 eq7080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7080 eq20004
  have eq20037 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq20006
       have i₂ := eq372 y
       grind)
    | exact superpose eq372 eq20006
    | exact resolve eq20006 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq20006
  have eq20076 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq20037
       grind)
    | exact superpose eq20037 eq10
    | exact resolve eq10 eq20037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20037
  have eq20148 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq20076
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20076
    | exact resolve eq20076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20076
  have eq20149 : x = (M.op y y) := by grind
  clear eq20148
  have eq20181 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7224 y
       have i₂ := eq20149
       grind)
    | exact superpose eq20149 eq7224
    | exact resolve eq7224 eq20149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7224
  have eq20227 : x = (M.op x y) := by
    first
    | (have i₁ := eq7703 y y
       have i₂ := eq20149
       grind)
    | exact superpose eq20149 eq7703
    | exact resolve eq7703 eq20149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7703 eq20149
  have eq21028 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20181
       grind)
    | exact superpose eq20181 eq16
    | exact resolve eq16 eq20181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20181
  have eq21111 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq21028
       have i₂ := eq20227
       grind)
    | exact superpose eq20227 eq21028
    | exact resolve eq21028 eq20227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20227 eq21028
  have eq21112 : False := by grind
  exact eq21112
