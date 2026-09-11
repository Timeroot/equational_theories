import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq67
  have eq401 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq406 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
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
  have eq409 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
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
  have eq418 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq401 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq401
    | (have j0 := eq401 X0 X1
       grind)
    | exact resolve eq401 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq825 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq418 x y
       grind)
    | exact superpose eq418 eq16
    | (have j1 := eq418 x y
       grind)
    | exact resolve eq16 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq418 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq2986 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq409 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq409
    | exact resolve eq409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq3035 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2986 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2986
    | (have j0 := eq2986 X0 X1
       grind)
    | exact resolve eq2986 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq3240 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq406 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq406
    | exact resolve eq406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq3300 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3240 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3240
    | (have j0 := eq3240 X0 X1
       grind)
    | exact resolve eq3240 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3240
  have eq3314 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X0 X0) ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3300 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq3300 X0 X1
       grind)
    | exact superpose eq3300 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq3300 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq3300 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3300 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq3300 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300
  have eq3343 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3314 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3314
  have eq3386 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq3343 X1 X0
       grind)
    | exact superpose eq3343 eq11
    | (have j1 := eq3343 X1 X0
       grind)
    | exact resolve eq11 eq3343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq3501 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3386 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3386
    | (have j0 := eq3386 X0 X1
       grind)
    | exact resolve eq3386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386
  have eq3521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3501 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3501
    | (have j0 := eq3501 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq3501 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3570 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq3501 (τ X0) X1
       grind)
    | exact superpose eq3501 eq18
    | (have j1 := eq3501 (τ X0) X1
       grind)
    | exact resolve eq18 eq3501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3501
  have eq3679 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3521 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq3521
    | (have j0 := eq3521 X0 X1
       grind)
    | exact resolve eq3521 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521
  have eq3935 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3570 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3570
    | exact resolve eq3570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3570
  have eq3992 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3935 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3935
    | (have j0 := eq3935 X0 X1
       grind)
    | exact resolve eq3935 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3935
  have eq11248 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3679 x y
       grind)
    | exact superpose eq3679 eq16
    | (have j1 := eq3679 x y
       grind)
    | exact resolve eq16 eq3679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11336 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq11248
       have i₂ := eq3992 x y
       grind)
    | exact superpose eq3992 eq11248
    | (have j1 := eq3992 x y
       grind)
    | (have r₁ := eq11248
       have r₂ := eq3992 x y
       grind)
    | (have r₁ := eq11248
       have r₂ := eq3992 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq11248
       have r₂ := eq3992 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11248 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq11337 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11248
       have i₂ := eq3035 x y
       grind)
    | exact superpose eq3035 eq11248
    | (have j1 := eq3035 x y
       grind)
    | (have r₁ := eq11248
       have r₂ := eq3035 x y
       grind)
    | (have r₁ := eq11248
       have r₂ := eq3035 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq11248
       have r₂ := eq3035 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11248 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035 eq11248
  have eq11338 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq11337
  have eq11339 : x = y ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq11336
  have eq11467 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11338
       grind)
    | exact superpose eq11338 eq16
    | exact resolve eq16 eq11338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11338
  have eq11468 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11467
       have r₂ := eq78 x
       grind)
    | exact resolve eq11467 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11467
  have eq11495 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11339
       grind)
    | exact superpose eq11339 eq16
    | exact resolve eq16 eq11339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11339
  have eq11496 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq11495
       have r₂ := eq78 x
       grind)
    | exact resolve eq11495 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11495
  have eq11501 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq832 x y
       have i₂ := eq11496
       grind)
    | exact superpose eq11496 eq832
    | (have j0 := eq832 x y
       grind)
    | exact resolve eq832 eq11496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11496
  have eq11518 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq11501
  have eq11519 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq11518
  have eq11527 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3679 x y
       have i₂ := eq11519
       grind)
    | exact superpose eq11519 eq3679
    | (have j0 := eq3679 x y
       grind)
    | exact resolve eq3679 eq11519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3679 eq11519
  have eq11543 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq11527
  have eq11555 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11543
       grind)
    | exact superpose eq11543 eq10
    | exact resolve eq10 eq11543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11543
  have eq11615 : x = y ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11555
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11555
    | exact resolve eq11555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11555
  have eq11617 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11615
       grind)
    | exact superpose eq11615 eq16
    | exact resolve eq16 eq11615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11615
  have eq11618 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq11617
       have r₂ := eq78 x
       grind)
    | exact resolve eq11617 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11617
  have eq11626 : (M.op y y) = (τ (σ (M.op x y))) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq11618
       grind)
    | exact superpose eq11618 eq10
    | exact resolve eq10 eq11618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11618
  have eq11686 : (M.op x y) = (M.op y y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11626
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq11626
    | exact resolve eq11626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11626
  have eq11689 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k X0 y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq11686
       grind)
    | exact superpose eq11686 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq11686
       grind)
    | exact resolve eq12 eq11686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11686
  have eq12613 : (M.op x y) = (k x y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have j0 := eq11689 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11689
  have eq12628 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq825
       have i₂ := eq12613
       grind)
    | exact superpose eq12613 eq825
    | exact resolve eq825 eq12613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq12613
  have eq12645 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq12628
  have eq12648 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq832 x y
       grind)
    | (have r₁ := eq12645
       have r₂ := eq832 x y
       grind)
    | exact resolve eq12645 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq12645
  have eq12652 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12648
       grind)
    | exact superpose eq12648 eq16
    | exact resolve eq16 eq12648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12648
  have eq12684 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12652
       have i₂ := eq11468
       grind)
    | exact superpose eq11468 eq12652
    | (have r₁ := eq12652
       have r₂ := eq11468
       grind)
    | exact resolve eq12652 eq11468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11468
  have eq12689 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq12684
  have eq12690 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq12689
  have eq12692 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq12690
       have r₂ := eq12652
       grind)
    | exact resolve eq12690 eq12652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12652 eq12690
  have eq12693 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12692
       grind)
    | exact superpose eq12692 eq16
    | exact resolve eq16 eq12692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12694 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12692
       grind)
    | exact superpose eq12692 eq10
    | exact resolve eq10 eq12692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12692
  have eq12756 : x = y := by
    first
    | (have i₁ := eq12694
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12694
    | exact resolve eq12694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12694
  have eq12757 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12693
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq12693
    | exact resolve eq12693 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq12693
  have eq12758 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12757
       have i₂ := eq12756
       grind)
    | exact superpose eq12756 eq12757
    | exact resolve eq12757 eq12756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12756 eq12757
  have eq12759 : False := by grind
  exact eq12759

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq413 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq416 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
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
  have eq3017 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq416
    | exact resolve eq416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq3060 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3017 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3017
    | (have j0 := eq3017 X0 X1
       grind)
    | exact resolve eq3017 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017
  have eq3308 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (σ X1) X0) = (M.op X0 X0) ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) X0
       have i₂ := eq413 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq413 X0 X1
       grind)
    | exact superpose eq413 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq413 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq413 (σ X1) X1
       grind)
    | (have r₁ := eq12 (σ X1) X0
       have r₂ := eq413 X0 X1
       grind)
    | exact resolve eq12 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3310 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq413 (σ x) y
       grind)
    | exact superpose eq413 eq16
    | (have j1 := eq413 (σ y) x
       grind)
    | (have r₁ := eq16
       have r₂ := eq413 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq3317 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308
  have eq3324 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3310
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq3310
    | exact resolve eq3310 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3310
  have eq3338 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3324
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3324
    | exact resolve eq3324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324
  have eq3594 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3317 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3317
    | exact resolve eq3317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317
  have eq3679 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3594 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3594
    | (have j0 := eq3594 X0 X1
       grind)
    | exact resolve eq3594 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3594
  have eq3706 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3679 X1 X0
       grind)
    | exact superpose eq3679 eq11
    | (have j1 := eq3679 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq3679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3679
  have eq3821 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3706 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3706
    | (have j0 := eq3706 X0 X1
       grind)
    | exact resolve eq3706 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3706
  have eq3841 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3821 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3821
    | (have j0 := eq3821 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3821 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3821
  have eq3999 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3841 X0 X1
       have i₂ := eq79 X1
       grind)
    | exact superpose eq79 eq3841
    | (have j0 := eq3841 X0 X1
       grind)
    | exact resolve eq3841 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3841
  have eq11694 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3999 y x
       grind)
    | exact superpose eq3999 eq16
    | (have j1 := eq3999 y x
       grind)
    | exact resolve eq16 eq3999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3999
  have eq11790 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11694
       have i₂ := eq3060 y x
       grind)
    | exact superpose eq3060 eq11694
    | (have j1 := eq3060 (σ (M.op x y)) (σ (M.op x x))
       grind)
    | (have r₁ := eq11694
       have r₂ := eq3060 y x
       grind)
    | (have r₁ := eq11694
       have r₂ := eq3060 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11694
       have r₂ := eq3060 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11694 eq3060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11694
  have eq11791 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq11790
  have eq11926 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11791
       grind)
    | exact superpose eq11791 eq16
    | exact resolve eq16 eq11791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11791
  have eq11927 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11926
       have r₂ := eq79 x
       grind)
    | exact resolve eq11926 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11926
  have eq11928 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3338
       have i₂ := eq11927
       grind)
    | exact superpose eq11927 eq3338
    | (have r₁ := eq3338
       have r₂ := eq11927
       grind)
    | exact resolve eq3338 eq11927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11927
  have eq11935 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq11928
  have eq11936 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq11935
  have eq11937 : (σ x) = (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq11936
       have r₂ := eq3338
       grind)
    | exact resolve eq11936 eq3338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338 eq11936
  have eq11939 : y = (τ (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11937
       grind)
    | exact superpose eq11937 eq10
    | exact resolve eq10 eq11937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11937
  have eq12002 : x = y ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11939
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11939
    | exact resolve eq11939 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11939
  have eq12004 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12002
       grind)
    | exact superpose eq12002 eq16
    | exact resolve eq16 eq12002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12002
  have eq12005 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq12004
       have r₂ := eq79 x
       grind)
    | exact resolve eq12004 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq12004
  have eq12021 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq12005
       grind)
    | exact superpose eq12005 eq11
    | exact resolve eq11 eq12005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12005
  have eq12120 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12021
       grind)
    | exact superpose eq12021 eq16
    | exact resolve eq16 eq12021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12021
  have eq12172 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq12120
       have i₂ := eq3060 y x
       grind)
    | exact superpose eq3060 eq12120
    | (have j1 := eq3060 x y
       grind)
    | (have r₁ := eq12120
       have r₂ := eq3060 y x
       grind)
    | (have r₁ := eq12120
       have r₂ := eq3060 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq12120
       have r₂ := eq3060 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq12120 eq3060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3060
  have eq12173 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq12172
  have eq12180 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq12120
       have i₂ := eq12173
       grind)
    | exact superpose eq12173 eq12120
    | exact resolve eq12120 eq12173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12173
  have eq12181 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq12180
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq12180
    | exact resolve eq12180 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq12180
  have eq12182 : (M.op x y) = (M.op x x) := by grind
  clear eq12181
  have eq12188 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq12182
       grind)
    | exact superpose eq12182 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12182
       grind)
    | exact resolve eq12 eq12182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12192 : (k y x) = (M.op x x) := by grind
  clear eq12188
  have eq12199 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12120
       have i₂ := eq12192
       grind)
    | exact superpose eq12192 eq12120
    | exact resolve eq12120 eq12192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12120 eq12192
  have eq12226 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12199
       have i₂ := eq12182
       grind)
    | exact superpose eq12182 eq12199
    | exact resolve eq12199 eq12182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12182 eq12199
  have eq12227 : False := by grind
  exact eq12227

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq269 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq275 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq276 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq378 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq276 (σ y) (σ x)
       grind)
    | exact superpose eq276 eq16
    | (have j1 := eq276 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq276 X1 X0
       grind)
    | exact superpose eq276 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq276 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq276 X0 X1
       grind)
    | exact resolve eq13 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq380 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq388 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq387 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq387 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq387 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq389 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq378
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq378
    | exact resolve eq378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq403 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
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
  have eq420 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq388 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq403 (τ X0) X1
       grind)
    | exact superpose eq403 eq17
    | (have j1 := eq403 (τ X0) X1
       grind)
    | exact resolve eq17 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq403
  have eq973 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq968 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq968
    | (have j0 := eq968 X0 X1
       grind)
    | exact resolve eq968 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq989 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq973 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq973
    | (have j0 := eq973 X0 X1
       grind)
    | exact resolve eq973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq992 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq989
    | (have j0 := eq989 X0 X1
       grind)
    | exact resolve eq989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1057 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq992 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq992
    | (have j0 := eq992 X1 (σ X0)
       grind)
    | exact resolve eq992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1444 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1057 X0 X0
       have i₂ := eq388 X0 (σ X0)
       grind)
    | exact superpose eq388 eq1057
    | (have j0 := eq1057 X1 X0
       have j1 := eq388 X0 (σ X1)
       grind)
    | exact resolve eq1057 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq1057
  have eq1482 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1444 X0 X1
       have j1 := eq420 X0 (σ X1)
       grind)
    | (have r₁ := eq1444 X0 X1
       have r₂ := eq420 X0 (σ X1)
       grind)
    | exact resolve eq1444 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq1444
  have eq1661 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1482 (σ X0) X1
       grind)
    | exact superpose eq1482 eq28
    | (have j1 := eq1482 (σ X0) X1
       grind)
    | exact resolve eq28 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1482
  have eq1672 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1661 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1661
    | (have j0 := eq1661 X0 X1
       grind)
    | exact resolve eq1661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661
  have eq1688 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1672 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1672
    | (have j0 := eq1672 X0 X1
       grind)
    | exact resolve eq1672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1697 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1688 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1688
    | (have j0 := eq1688 X0 X1
       grind)
    | exact resolve eq1688 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1786 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1697 x y
       grind)
    | exact superpose eq1697 eq16
    | (have j1 := eq1697 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1697 x y
       grind)
    | exact resolve eq16 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq1809 : x = (k x y) := by grind
  clear eq1786
  have eq1988 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq389
       have i₂ := eq276 y x
       grind)
    | exact superpose eq276 eq389
    | (have j1 := eq276 y x
       grind)
    | exact resolve eq389 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1991 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1988
  have eq1992 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1991
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq1991
    | exact resolve eq1991 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq1993 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1992
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq1992
    | exact resolve eq1992 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq1994 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq389
       have i₂ := eq1993
       grind)
    | exact superpose eq1993 eq389
    | exact resolve eq389 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq1993
  have eq2006 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1994
  have eq2007 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2006
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq2006
    | exact resolve eq2006 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2008 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2007
  have eq2010 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2008
       grind)
    | exact superpose eq2008 eq16
    | exact resolve eq16 eq2008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2039 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2010
       have i₂ := eq276 y x
       grind)
    | exact superpose eq276 eq2010
    | (have j1 := eq276 y x
       grind)
    | exact resolve eq2010 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq2042 : (M.op x y) = (k x y) := by grind
  clear eq2039
  have eq2044 : x = (M.op x y) := by
    first
    | (have i₁ := eq2042
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq2042
    | exact resolve eq2042 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809 eq2042
  have eq2045 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2010
       have i₂ := eq2044
       grind)
    | exact superpose eq2044 eq2010
    | exact resolve eq2010 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010 eq2044
  have eq2059 : False := by grind
  exact eq2059

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq282 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
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
  have eq285 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq286 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq285 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq291 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq292 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq535 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq292
    | exact resolve eq292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq292 x y
       grind)
    | exact superpose eq292 eq16
    | (have j1 := eq292 x y
       grind)
    | exact resolve eq16 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq558 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq535
    | (have j0 := eq535 X0 X1
       grind)
    | exact resolve eq535 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq535
  have eq560 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq558
    | exact resolve eq558 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq619 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq560 (τ X0) X1
       grind)
    | exact superpose eq560 eq18
    | (have j1 := eq560 (τ X0) X1
       grind)
    | exact resolve eq18 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq560
  have eq858 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq619 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq619
    | exact resolve eq619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq911 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq858 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq858
    | (have j0 := eq858 X0 X1
       grind)
    | exact resolve eq858 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq996 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq543
       have i₂ := eq911 x y
       grind)
    | exact superpose eq911 eq543
    | (have j1 := eq911 (σ x) (σ y)
       grind)
    | (have r₁ := eq543
       have r₂ := eq911 x y
       grind)
    | exact resolve eq543 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq996
  have eq1002 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq997
  have eq1034 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq543
       have i₂ := eq1002
       grind)
    | exact superpose eq1002 eq543
    | exact resolve eq543 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq1002
  have eq1035 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1034
  have eq1036 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1035
  have eq1045 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1036
  have eq1057 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1045
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1045
    | exact resolve eq1045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1100 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1057
       grind)
    | exact superpose eq1057 eq16
    | exact resolve eq16 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1114 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1100
       have i₂ := eq911 x y
       grind)
    | exact superpose eq911 eq1100
    | (have j1 := eq911 x y
       grind)
    | (have r₁ := eq1100
       have r₂ := eq911 x y
       grind)
    | exact resolve eq1100 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq1115 : x = (M.op y y) := by grind
  clear eq1114
  have eq1158 : (M.op x y) = (k x y) := by grind
  clear eq1115
  have eq1168 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1100
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq1100
    | exact resolve eq1100 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100 eq1158
  have eq1171 : False := by grind
  exact eq1171

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq88 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq306 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq824 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ X1)) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq306
    | (have j0 := eq306 (σ X1) (σ X0)
       grind)
    | exact resolve eq306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq5707 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq88 (σ X1) X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5735 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq88 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq5736 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5735 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5735
  have eq5737 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5707 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5707
  have eq5738 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5737 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5737
  have eq5740 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5736 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5736
    | (have j0 := eq5736 X0
       grind)
    | exact resolve eq5736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5736
  have eq5785 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq5740 X0
       grind)
    | exact superpose eq5740 eq39
    | (have j1 := eq5740 X0
       grind)
    | exact resolve eq39 eq5740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5740
  have eq5827 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5785 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5785
    | (have j0 := eq5785 X0
       grind)
    | exact resolve eq5785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5785
  have eq5828 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5827 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5827
  have eq5894 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5828 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5828
    | exact resolve eq5828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5921 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq5828 X0
       grind)
    | exact superpose eq5828 eq11
    | exact resolve eq11 eq5828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5828
  have eq5986 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5894 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq5894
    | exact resolve eq5894 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5894
  have eq6005 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq5986 X0
       grind)
    | exact superpose eq5986 eq11
    | exact resolve eq11 eq5986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6118 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6005 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq6005
    | exact resolve eq6005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6005
  have eq6310 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq6118 (τ X0)
       grind)
    | exact superpose eq6118 eq35
    | exact resolve eq35 eq6118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6364 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6310 X0
       have i₂ := eq5986 X0
       grind)
    | exact superpose eq5986 eq6310
    | exact resolve eq6310 eq5986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5986 eq6310
  have eq6551 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq6610 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq6551 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq6551
    | exact resolve eq6551 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6551
  have eq6645 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6610 X0
       have i₂ := eq6118 X0
       grind)
    | exact superpose eq6118 eq6610
    | exact resolve eq6610 eq6118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6610
  have eq6660 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq6645
  have eq40257 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) X0
       have i₂ := eq5738 (σ X0) X1
       grind)
    | exact superpose eq5738 eq25
    | (have j1 := eq5738 (σ X0) X1
       grind)
    | exact resolve eq25 eq5738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq5738
  have eq40343 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40257 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq40257
    | (have j0 := eq40257 X0 X1
       grind)
    | exact resolve eq40257 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40257
  have eq40418 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40343 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40343
    | (have j0 := eq40343 X0 X1
       grind)
    | exact resolve eq40343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40343
  have eq40483 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40418 X0 X1
       have i₂ := eq5921 X0
       grind)
    | exact superpose eq5921 eq40418
    | (have j0 := eq40418 X0 X1
       grind)
    | exact resolve eq40418 eq5921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40418
  have eq40526 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40483 X0 X1
       have i₂ := eq6118 X0
       grind)
    | exact superpose eq6118 eq40483
    | (have j0 := eq40483 X0 X1
       grind)
    | exact resolve eq40483 eq6118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40483
  have eq40561 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40526 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40526
    | (have j0 := eq40526 X0 X1
       grind)
    | exact resolve eq40526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40526
  have eq42089 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq824 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq824
    | (have j0 := eq824 (τ X0) (τ X1)
       grind)
    | exact resolve eq824 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq42199 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42089 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq42089
    | (have j0 := eq42089 X0 X1
       grind)
    | exact resolve eq42089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42089
  have eq42287 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42199 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq42199
    | (have j0 := eq42199 X0 X1
       grind)
    | exact resolve eq42199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42199
  have eq42373 : ∀ X0 X1 : G, (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42287 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42287
    | (have j0 := eq42287 X0 X1
       grind)
    | exact resolve eq42287 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42287
  have eq42452 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42373 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42373
    | (have j0 := eq42373 X0 X1
       grind)
    | exact resolve eq42373 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42373
  have eq42507 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42452 X0 X1
       have i₂ := eq5921 (σ (τ X1))
       grind)
    | exact superpose eq5921 eq42452
    | (have j0 := eq42452 X0 X1
       grind)
    | exact resolve eq42452 eq5921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5921 eq42452
  have eq42558 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42507 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq42507
    | (have j0 := eq42507 X0 X1
       grind)
    | exact resolve eq42507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42507
  have eq42603 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42558 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq42558
    | (have j0 := eq42558 X0 X1
       grind)
    | exact resolve eq42558 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq42558
  have eq42636 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42603 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq42603
    | (have j0 := eq42603 X0 X1
       grind)
    | exact resolve eq42603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42603
  have eq42663 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42636 X0 X1
       have i₂ := eq6118 X1
       grind)
    | exact superpose eq6118 eq42636
    | (have j0 := eq42636 X0 X1
       grind)
    | exact resolve eq42636 eq6118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6118 eq42636
  have eq42689 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42663 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42663
    | (have j0 := eq42663 X0 X1
       grind)
    | exact resolve eq42663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42663
  have eq46060 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq40561 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40561
    | (have j0 := eq40561 X1 (τ X0)
       grind)
    | exact resolve eq40561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46124 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq40561 X1 X0
       grind)
    | exact superpose eq40561 eq11
    | (have j1 := eq40561 X1 X0
       grind)
    | exact resolve eq11 eq40561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40561
  have eq47605 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46060 X1 (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq46060
    | (have j0 := eq46060 X0 (τ X1)
       grind)
    | exact resolve eq46060 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq46060
  have eq47800 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47605 X0 X1
       have i₂ := eq6364 X1
       grind)
    | exact superpose eq6364 eq47605
    | (have j0 := eq47605 X0 X1
       grind)
    | exact resolve eq47605 eq6364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6364 eq47605
  have eq47884 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47800 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq47800
    | (have j0 := eq47800 X0 X1
       grind)
    | exact resolve eq47800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47800
  have eq47956 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47884 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq47884
    | (have j0 := eq47884 X0 X1
       grind)
    | exact resolve eq47884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47884
  have eq48347 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47956 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47956
  have eq51325 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46124 y x
       grind)
    | exact superpose eq46124 eq16
    | (have j1 := eq46124 y x
       grind)
    | exact resolve eq16 eq46124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46124
  have eq52629 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51325
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq51325
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq51325 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51325
  have eq52632 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq52629
  have eq52633 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq52632
  have eq52658 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48347 y x
       have i₂ := eq52633
       grind)
    | exact superpose eq52633 eq48347
    | (have j0 := eq48347 y x
       grind)
    | exact resolve eq48347 eq52633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48347
  have eq52659 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq52658
  have eq52660 : y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq52659
  have eq53390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6660 x
       have i₂ := eq52660
       grind)
    | exact superpose eq52660 eq6660
    | exact resolve eq6660 eq52660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52660
  have eq53443 : (σ y) = (σ (M.op x x)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq53390
       have r₂ := eq16
       grind)
    | exact resolve eq53390 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53390
  have eq54136 : (M.op x x) = (τ (σ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq53443
       grind)
    | exact superpose eq53443 eq10
    | exact resolve eq10 eq53443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53443
  have eq54293 : y = (M.op x x) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq54136
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq54136
    | exact resolve eq54136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54136
  have eq54397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq6660 x
       have i₂ := eq54293
       grind)
    | exact superpose eq54293 eq6660
    | exact resolve eq6660 eq54293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54293
  have eq54450 : (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq54397
       have r₂ := eq16
       grind)
    | exact resolve eq54397 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54397
  have eq55138 : (k y x) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq54450
       grind)
    | exact superpose eq54450 eq11
    | exact resolve eq11 eq54450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54450
  have eq55329 : x = (k y x) := by
    first
    | (have i₁ := eq55138
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq55138
    | exact resolve eq55138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55138
  have eq55403 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq42689 y x
       have i₂ := eq55329
       grind)
    | exact superpose eq55329 eq42689
    | (have j0 := eq42689 y x
       grind)
    | exact resolve eq42689 eq55329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42689 eq55329
  have eq55404 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq55403
  have eq60445 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55404
       grind)
    | exact superpose eq55404 eq16
    | exact resolve eq16 eq55404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55404
  have eq61490 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq60445
       have i₂ := eq52633
       grind)
    | exact superpose eq52633 eq60445
    | exact resolve eq60445 eq52633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52633 eq60445
  have eq61491 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq61490
  have eq61492 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq61491
  have eq61518 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6660 x
       have i₂ := eq61492
       grind)
    | exact superpose eq61492 eq6660
    | exact resolve eq6660 eq61492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61492
  have eq61573 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq61518
       have r₂ := eq16
       grind)
    | exact resolve eq61518 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61518
  have eq62377 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq61573
       grind)
    | exact superpose eq61573 eq10
    | exact resolve eq10 eq61573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61573
  have eq62538 : y = (M.op x x) := by
    first
    | (have i₁ := eq62377
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq62377
    | exact resolve eq62377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62377
  have eq62673 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6660 x
       have i₂ := eq62538
       grind)
    | exact superpose eq62538 eq6660
    | exact resolve eq6660 eq62538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6660 eq62538
  have eq62732 : False := by grind
  exact eq62732

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq59 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq18
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq62 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
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
  clear eq56
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq62
    | exact resolve eq62 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq62
  have eq79 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
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
  have eq83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq90
  have eq261 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | (have j0 := eq92 X1 X1
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq281 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq261
    | (have j0 := eq261 X0 X1
       grind)
    | exact resolve eq261 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq261
  have eq287 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X1
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq281 X0 X0
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq281 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq281
  have eq291 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq287 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq287
    | (have j0 := eq287 X0 X1
       grind)
    | exact resolve eq287 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq287
  have eq380 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq291
    | exact resolve eq291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq425 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq380 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq380 X0 X1
       grind)
    | exact superpose eq380 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq380 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq380 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq380 X0 X1
       grind)
    | exact resolve eq13 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq432 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq430 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq430 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq430 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq475 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq432 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq479 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq475 X0 X1
       have j1 := eq380 X1 X0
       grind)
    | (have r₁ := eq475 X0 X0
       have r₂ := eq380 X0 X0
       grind)
    | (have r₁ := eq475 X1 X0
       have r₂ := eq380 X0 X1
       grind)
    | exact resolve eq475 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq475
  have eq588 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq479 (σ X1) (σ X0)
       grind)
    | exact superpose eq479 eq15
    | exact resolve eq15 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq588 X0 X1
       have i₂ := eq479 X1 X0
       grind)
    | exact superpose eq479 eq588
    | exact resolve eq588 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq588
  have eq1010 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq607 x y
       grind)
    | exact superpose eq607 eq16
    | (have r₁ := eq16
       have r₂ := eq607 x y
       grind)
    | exact resolve eq16 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq1025 : False := by grind
  exact eq1025

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X0)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X1 (M.op X1 X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq63
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq13
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq129 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 (M.op X1 (M.op X1 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 (M.op X1 (M.op X1 X0))) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq263 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 X1 X1
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq281 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq263
    | (have j0 := eq263 X0 X1
       grind)
    | exact resolve eq263 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq287 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X1
       have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq281 X0 X0
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq281 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq382 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq287 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq287
    | exact resolve eq287 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq287 (σ X1) X0
       grind)
    | exact superpose eq287 eq15
    | (have j1 := eq287 (σ X1) X0
       grind)
    | exact resolve eq15 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq406 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq382 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq382
    | (have j0 := eq382 X0 X1
       grind)
    | exact resolve eq382 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq382
  have eq426 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq406 X0 (τ X1)
       grind)
    | exact superpose eq406 eq17
    | (have j1 := eq406 X0 (τ X1)
       grind)
    | exact resolve eq17 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq406
  have eq492 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op X1 (M.op X1 (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq129 (σ X0) X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq129
    | exact resolve eq129 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq969 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq426
    | exact resolve eq426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq1014 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq969 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq969
    | (have j0 := eq969 X0 X1
       grind)
    | exact resolve eq969 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq3748 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq393 x y
       grind)
    | exact superpose eq393 eq16
    | (have j1 := eq393 x y
       grind)
    | exact resolve eq16 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3780 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq393 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq3820 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3748
       have i₂ := eq1014 y x
       grind)
    | exact superpose eq1014 eq3748
    | (have j1 := eq1014 y x
       grind)
    | (have r₁ := eq3748
       have r₂ := eq1014 y x
       grind)
    | exact resolve eq3748 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748
  have eq3821 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3820
  have eq3887 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3821
       grind)
    | exact superpose eq3821 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3821
       grind)
    | exact resolve eq13 eq3821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3821
  have eq3898 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3887
  have eq24738 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3780 x y
       have i₂ := eq3898
       grind)
    | exact superpose eq3898 eq3780
    | (have j0 := eq3780 x y
       grind)
    | exact resolve eq3780 eq3898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3780 eq3898
  have eq24749 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq24738
  have eq24750 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq24749
  have eq24878 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24750
       grind)
    | exact superpose eq24750 eq16
    | exact resolve eq16 eq24750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24879 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq79 x (σ y)
       have i₂ := eq24750
       grind)
    | exact superpose eq24750 eq79
    | (have j0 := eq79 x (σ y)
       grind)
    | (have r₁ := eq79 x (σ y)
       have r₂ := eq24750
       grind)
    | exact resolve eq79 eq24750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq24750
  have eq24906 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq24879
  have eq24916 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24906
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq24906
    | exact resolve eq24906 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24906
  have eq25407 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1014 y x
       have i₂ := eq24916
       grind)
    | exact superpose eq24916 eq1014
    | (have j0 := eq1014 y x
       grind)
    | exact resolve eq1014 eq24916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq24916
  have eq25513 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq25407
       have r₂ := eq24878
       grind)
    | exact resolve eq25407 eq24878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25407
  have eq25673 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24878
       have i₂ := eq25513
       grind)
    | exact superpose eq25513 eq24878
    | exact resolve eq24878 eq25513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24878 eq25513
  have eq25697 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq25673
  have eq25698 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq25697
  have eq25821 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq80 x X0
       have i₂ := eq25698
       grind)
    | exact superpose eq25698 eq80
    | (have j0 := eq80 x X0
       grind)
    | (have r₁ := eq80 x x
       have r₂ := eq25698
       grind)
    | exact resolve eq80 eq25698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25830 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op X0 (M.op X0 (σ x)))))) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq492 x x
       have i₂ := eq25698
       grind)
    | exact superpose eq25698 eq492
    | exact resolve eq492 eq25698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq25698
  have eq25873 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq25821 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25821
  have eq25889 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq25830 x
       have i₂ := eq9 (σ x) x
       grind)
    | exact superpose eq9 eq25830
    | exact resolve eq25830 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25830
  have eq25894 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq25873 X0
       have j1 := eq80 x X0
       grind)
    | (have r₁ := eq25873 X0
       have r₂ := eq80 x x
       grind)
    | exact resolve eq25873 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq25873
  have eq25905 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq25889
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq25889
    | exact resolve eq25889 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq25889
  have eq25906 : (σ x) = (σ (M.op x x)) := by grind
  clear eq25905
  have eq25922 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq25906
       grind)
    | exact superpose eq25906 eq10
    | exact resolve eq10 eq25906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25906
  have eq26030 : x = (M.op x x) := by
    first
    | (have i₁ := eq25922
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25922
    | exact resolve eq25922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25922
  have eq26289 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq26030
       grind)
    | exact superpose eq26030 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq26030
       grind)
    | exact resolve eq12 eq26030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26030
  have eq26346 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq26289 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26289
  have eq27205 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq25894 (σ X0)
       grind)
    | exact superpose eq25894 eq15
    | exact resolve eq15 eq25894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25894
  have eq27310 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq27205 X0
       have i₂ := eq26346 X0
       grind)
    | exact superpose eq26346 eq27205
    | exact resolve eq27205 eq26346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26346 eq27205
  have eq28079 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27310 y
       grind)
    | exact superpose eq27310 eq16
    | (have r₁ := eq16
       have r₂ := eq27310 y
       grind)
    | exact resolve eq16 eq27310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27310
  have eq28208 : False := by grind
  exact eq28208

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq349 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq351 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq352 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq349 X0 X1
       have j1 := eq351 X0 X1
       grind)
    | (have r₁ := eq349 X0 X1
       have r₂ := eq351 X0 X1
       grind)
    | exact resolve eq349 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq351
  have eq402 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
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
  have eq406 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq352 x (σ y)
       grind)
    | exact superpose eq352 eq16
    | (have j1 := eq352 x (σ y)
       grind)
    | exact resolve eq16 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq425 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq406
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq406
    | exact resolve eq406 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq433 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq402 X0 X1
       grind)
    | exact superpose eq402 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq402 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq402 X0 X1
       grind)
    | exact resolve eq13 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq445 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq443 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq443 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq443 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq473 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq445 X0 (τ X1)
       grind)
    | exact superpose eq445 eq17
    | (have j1 := eq445 X0 (τ X1)
       grind)
    | exact resolve eq17 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq479 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq445 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1640 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq473 (τ X0) X1
       grind)
    | exact superpose eq473 eq18
    | (have j1 := eq473 (τ X0) X1
       grind)
    | exact resolve eq18 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq473
  have eq1647 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1640 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1640
    | (have j0 := eq1640 X0 X1
       grind)
    | exact resolve eq1640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640
  have eq1667 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1647 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1647
    | (have j0 := eq1647 X0 X1
       grind)
    | exact resolve eq1647 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1672 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1667 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1667
    | (have j0 := eq1667 X0 X1
       grind)
    | exact resolve eq1667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq1746 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1672 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1672
    | (have j0 := eq1672 X1 (σ X0)
       grind)
    | exact resolve eq1672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq2185 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1746 X0 X0
       have i₂ := eq445 X0 (σ X0)
       grind)
    | exact superpose eq445 eq1746
    | (have j0 := eq1746 X1 X0
       have j1 := eq445 X0 (σ X1)
       grind)
    | exact resolve eq1746 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq1746
  have eq2224 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2185 X0 X1
       have j1 := eq479 (σ X1) X0
       grind)
    | (have r₁ := eq2185 X1 X1
       have r₂ := eq479 (σ X1) X1
       grind)
    | exact resolve eq2185 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq2185
  have eq2328 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq2224 (σ X0) X1
       grind)
    | exact superpose eq2224 eq22
    | (have j1 := eq2224 (σ X0) X1
       grind)
    | exact resolve eq22 eq2224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2224
  have eq2338 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2328 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2328
    | (have j0 := eq2328 X0 X1
       grind)
    | exact resolve eq2328 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328
  have eq2353 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2338 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2338
    | (have j0 := eq2338 X0 X1
       grind)
    | exact resolve eq2338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338
  have eq2362 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2353 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2353
    | (have j0 := eq2353 X0 X1
       grind)
    | exact resolve eq2353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2542 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2362 x y
       grind)
    | exact superpose eq2362 eq16
    | (have j1 := eq2362 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2362 x y
       grind)
    | exact resolve eq16 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq2581 : x = (k y x) := by grind
  clear eq2542
  have eq3103 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq425
       have i₂ := eq402 x y
       grind)
    | exact superpose eq402 eq425
    | (have j1 := eq402 x y
       grind)
    | exact resolve eq425 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3104 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq3103
  have eq3105 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq3104
       have i₂ := eq2581
       grind)
    | exact superpose eq2581 eq3104
    | exact resolve eq3104 eq2581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104
  have eq3106 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3105
       have i₂ := eq2581
       grind)
    | exact superpose eq2581 eq3105
    | exact resolve eq3105 eq2581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105
  have eq3107 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq425
       have i₂ := eq3106
       grind)
    | exact superpose eq3106 eq425
    | exact resolve eq425 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq3106
  have eq3120 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3107
  have eq3121 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3120
       have i₂ := eq2581
       grind)
    | exact superpose eq2581 eq3120
    | exact resolve eq3120 eq2581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3122 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3121
  have eq3124 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3122
       grind)
    | exact superpose eq3122 eq16
    | exact resolve eq16 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3122
  have eq3168 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq3124
       have i₂ := eq402 x y
       grind)
    | exact superpose eq402 eq3124
    | (have j1 := eq402 x y
       grind)
    | exact resolve eq3124 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq3169 : (M.op x y) = (k y x) := by grind
  clear eq3168
  have eq3171 : x = (M.op x y) := by
    first
    | (have i₁ := eq3169
       have i₂ := eq2581
       grind)
    | exact superpose eq2581 eq3169
    | exact resolve eq3169 eq2581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2581 eq3169
  have eq3172 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3124
       have i₂ := eq3171
       grind)
    | exact superpose eq3171 eq3124
    | exact resolve eq3124 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124 eq3171
  have eq3187 : False := by grind
  exact eq3187
