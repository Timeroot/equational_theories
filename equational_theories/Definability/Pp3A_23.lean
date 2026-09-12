import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyx_pxx_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq43 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
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
  have eq51 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq14 X2 (M.op X2 x) X4 X5
       have i₂ := eq14 X2 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 x x X4 X5
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq158 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq135 eq16
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq230 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq215 eq229
    | exact resolve eq229 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq233 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq230 eq14
    | exact resolve eq14 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq233 x x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq233
    | exact resolve eq233 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq236 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq215 eq234
    | exact resolve eq234 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq260 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq283 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq395 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq415 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq230 eq395
    | exact resolve eq395 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq492 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq51 x x X2 X4 X5
       have i₂ := eq415 x x
       grind)
    | exact superpose eq415 eq51
    | exact resolve eq51 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq493 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq492 X2 x x
       have i₂ := eq415 x x
       grind)
    | exact superpose eq415 eq492
    | exact resolve eq492 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq499 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) = X0 ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq493 eq12
    | (have j0 := eq12 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq12 x (M.op x (M.op x y))
       have r₂ := eq493 x
       grind)
    | exact resolve eq12 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) = (k (M.op x (M.op x y)) (M.op x (M.op x y))) := by grind
  have eq510 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) = X0 ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq512 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq493 eq506
    | exact resolve eq506 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq518 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) ∨ (M.op x (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq493 eq510
    | (have j0 := eq510 X0
       grind)
    | exact resolve eq510 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq521 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq55 x x X2 X3 X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq522 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq215 eq521
    | exact resolve eq521 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq523 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq522 x x X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq522
    | exact resolve eq522 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq524 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq215 eq523
    | exact resolve eq523 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq568 : (k x (k (M.op x y) (M.op x y))) = (τ (k (σ x) (k (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq158 eq283
    | exact resolve eq283 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq283
  have eq661 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq662 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq765 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq260
  have eq776 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq765 X0
       have i₂ := eq56 (σ X0) (σ X0)
       grind)
    | exact superpose eq56 eq765
    | exact resolve eq765 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq784 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq215 eq776
    | exact resolve eq776 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq3819 : (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq512 eq662
    | (have j0 := eq662 (M.op x (M.op x y))
       grind)
    | exact resolve eq662 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq3827 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by grind
  clear eq3819
  have eq17882 : (τ (M.op x (M.op x y))) = (k (τ (σ (M.op x (M.op x y)))) (M.op x (M.op x y))) := by
    first
    | exact superpose eq3827 eq784
    | exact resolve eq784 eq3827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq17890 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3827 eq415
    | exact resolve eq415 eq3827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17893 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq3827 eq17890
    | exact resolve eq17890 eq3827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17890
  have eq17900 : (k (M.op x (M.op x y)) (M.op x (M.op x y))) = (τ (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq17882
       have i₂ := eq16 (M.op x sF0)
       grind)
    | exact superpose eq16 eq17882
    | exact resolve eq17882 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17882
  have eq17907 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq512 eq17900
    | exact resolve eq17900 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17900
  have eq19052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19052
    | exact resolve eq19052 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19052
  have eq19064 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19053
       have r₂ := eq28
       grind)
    | exact resolve eq19053 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19053
  have eq19067 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq19064
  have eq19079 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19067
    | exact resolve eq19067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19067
  have eq19088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19079 eq100
    | exact resolve eq100 eq19079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq19079
  have eq19101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq19088
  have eq19104 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq19101
       have r₂ := eq28
       grind)
    | exact resolve eq19101 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19101
  have eq19414 : (M.op (M.op x y) y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19104 eq56
    | exact resolve eq56 eq19104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19418 : (M.op x (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq215 eq19414
    | exact resolve eq19414 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19414
  have eq19752 : (σ x) = (M.op x (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19418 eq19104
    | exact resolve eq19104 eq19418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19104 eq19418
  have eq19761 : (σ x) = (M.op x (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq19752
  have eq19771 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19761 eq236
    | exact resolve eq236 eq19761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19782 : (σ x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19761 eq17907
    | exact resolve eq17907 eq19761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17907 eq19761
  have eq19813 : y = (M.op x x) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq19782
    | exact resolve eq19782 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19782
  have eq19814 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq19771
    | exact resolve eq19771 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19771
  have eq19817 : (M.op x y) = (k y x) ∨ x = (σ x) ∨ x = (M.op y x) := by grind
  have eq19822 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq19813
       grind)
    | exact superpose eq19813 eq56
    | exact resolve eq56 eq19813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19823 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq415 x x
       have i₂ := eq19813
       grind)
    | exact superpose eq19813 eq415
    | exact resolve eq415 eq19813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19824 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq215 eq19822
    | exact resolve eq19822 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19822
  have eq19828 : (M.op x y) = (k y x) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19817
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19817
    | exact resolve eq19817 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19817
  have eq19830 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19824
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19824
    | exact resolve eq19824 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19824
  have eq19838 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq19814
       grind)
    | exact superpose eq19814 eq56
    | exact resolve eq56 eq19814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19839 : (M.op y x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq415 x x
       have i₂ := eq19814
       grind)
    | exact superpose eq19814 eq415
    | exact resolve eq415 eq19814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19840 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq215 eq19838
    | exact resolve eq19838 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19838
  have eq19846 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19840
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19840
    | exact resolve eq19840 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19840
  have eq19849 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq19828
       grind)
    | exact superpose eq19828 eq74
    | exact resolve eq74 eq19828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq19828
  have eq19877 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq19849
    | exact resolve eq19849 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19849
  have eq19909 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq19830 eq493
    | exact resolve eq493 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19910 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19830 eq512
    | exact resolve eq512 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19911 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 ∨ x = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq19830 eq518
    | exact resolve eq518 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19830
  have eq20340 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq19846 eq493
    | exact resolve eq493 eq19846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20341 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19846 eq512
    | exact resolve eq512 eq19846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20349 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19846 eq17893
    | exact resolve eq17893 eq19846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19846
  have eq20384 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq20349
    | exact resolve eq20349 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20349
  have eq20391 : (M.op (M.op x y) y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq20384
       grind)
    | exact superpose eq20384 eq56
    | exact resolve eq56 eq20384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20395 : (M.op y x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq215 eq20391
    | exact resolve eq20391 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20391
  have eq20776 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by grind
  have eq20782 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq19909 eq56
    | exact resolve eq56 eq19909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19909
  have eq20834 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq215 eq20782
    | exact resolve eq20782 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20782
  have eq20847 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19910 eq135
    | exact resolve eq135 eq19910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19910
  have eq20890 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq20847
    | exact resolve eq20847 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20847
  have eq21082 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  have eq21088 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20340 eq56
    | exact resolve eq56 eq20340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20340
  have eq21140 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq215 eq21088
    | exact resolve eq21088 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21088
  have eq21200 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20341 eq135
    | exact resolve eq135 eq20341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20341
  have eq21243 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq21200
    | exact resolve eq21200 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21200
  have eq49503 : x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq20384
       have i₂ := eq20395
       grind)
    | exact superpose eq20395 eq20384
    | exact resolve eq20384 eq20395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20384 eq20395
  have eq49512 : x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq49503
  have eq49546 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq49512 eq3827
    | exact resolve eq3827 eq49512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827 eq49512
  have eq49593 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq49546
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq49546
    | exact resolve eq49546 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49546
  have eq51379 : (M.op x (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq49593 eq415
    | exact resolve eq415 eq49593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58274 : (τ (k (σ x) (σ (M.op x y)))) = (k x (k (M.op x y) (M.op x y))) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20890 eq568
    | exact resolve eq568 eq20890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20890
  have eq58351 : (k x (M.op x y)) = (k x (k (M.op x y) (M.op x y))) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq66 eq58274
    | exact resolve eq58274 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58274
  have eq58389 : (τ (k (σ x) (σ (M.op x y)))) = (k x (k (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21243 eq568
    | exact resolve eq568 eq21243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq21243
  have eq58444 : (k x (M.op x y)) = (k x (k (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq66 eq58389
    | exact resolve eq58389 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58389
  have eq61698 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq51379 eq49593
    | exact resolve eq49593 eq51379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49593 eq51379
  have eq61714 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq61698
  have eq62072 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq61714 eq236
    | exact resolve eq236 eq61714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61714
  have eq62149 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27 eq62072
    | exact resolve eq62072 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62072
  have eq62150 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq62149
  have eq62154 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62150 eq230
    | exact resolve eq230 eq62150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62171 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27 eq62154
    | exact resolve eq62154 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62154
  have eq62191 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq62171 eq493
    | exact resolve eq493 eq62171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq62192 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62171 eq512
    | exact resolve eq512 eq62171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq62202 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62171 eq17893
    | exact resolve eq17893 eq62171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62171
  have eq62263 : (σ x) = (σ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62150 eq62202
    | exact resolve eq62202 eq62150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62202
  have eq62337 : (σ x) = (σ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq62263
  have eq63244 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq62150 eq62191
    | exact resolve eq62191 eq62150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62191
  have eq63290 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq63244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63244
  have eq63306 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62150 eq62192
    | exact resolve eq62192 eq62150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62150 eq62192
  have eq63328 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq63306
  have eq63741 : (σ x) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq63290 (M.op x sF2)
       have i₂ := eq415 x sF2
       grind)
    | exact superpose eq415 eq63290
    | exact resolve eq63290 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63766 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq63290 eq56
    | exact resolve eq56 eq63290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63290
  have eq63805 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq215 eq63766
    | exact resolve eq63766 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63766
  have eq64155 : (τ (σ x)) = (k x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq63328 eq50
    | exact resolve eq50 eq63328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq63328
  have eq64203 : x = (k x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29 eq64155
    | exact resolve eq64155 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64155
  have eq65698 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq64203
       grind)
    | exact superpose eq64203 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq64203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64203
  have eq65699 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq65698
  have eq66081 : (M.op x x) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq415 x x
       have i₂ := eq65699
       grind)
    | exact superpose eq65699 eq415
    | exact resolve eq415 eq65699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71176 : ∀ X0 : G, (M.op x x) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq66081 eq63805
    | exact resolve eq63805 eq66081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63805 eq66081
  have eq71189 : ∀ X0 : G, (M.op x x) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq71176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71176
  have eq74130 : ∀ X0 : G, x = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq65699
       have i₂ := eq71189 X0
       grind)
    | exact superpose eq71189 eq65699
    | exact resolve eq65699 eq71189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65699 eq71189
  have eq74214 : ∀ X0 : G, x = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq74130 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74130
  have eq74273 : x = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq74214 (M.op x sF2)
       have i₂ := eq415 x sF2
       grind)
    | exact superpose eq415 eq74214
    | exact resolve eq74214 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74214
  have eq74771 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq74273 eq524
    | exact resolve eq524 eq74273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74273
  have eq75769 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq415 x X0
       have i₂ := eq74771 X0
       grind)
    | exact superpose eq74771 eq415
    | exact resolve eq415 eq74771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq74771
  have eq94192 : ∀ X0 : G, (σ x) = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq63741
       have i₂ := eq75769 sF0
       grind)
    | exact superpose eq75769 eq63741
    | exact resolve eq63741 eq75769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63741 eq75769
  have eq94277 : ∀ X0 : G, (σ x) = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq94192 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94192
  have eq94354 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq94277 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94277
    | (have j0 := eq94277 y
       grind)
    | exact resolve eq94277 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94277
  have eq95399 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq94354 eq62337
    | exact resolve eq62337 eq94354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62337 eq94354
  have eq95485 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq95399
  have eq95515 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq95485
    | exact resolve eq95485 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq95485
  have eq95516 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq95515
  have eq95518 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq95516 eq31
    | exact resolve eq31 eq95516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq278644 : x ≠ (M.op x (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by grind
  clear eq19823
  have eq278732 : x ≠ (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq19839
  have eq294001 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) ∨ x = (σ x) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq20834 eq20834
    | exact resolve eq20834 eq20834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20834
  have eq294219 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq294001 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294001
  have eq300243 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21082 eq135
    | exact resolve eq135 eq21082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq21082
  have eq300351 : (k (M.op x y) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq95516 eq300243
    | exact resolve eq300243 eq95516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300243
  have eq539997 : (k (M.op x y) (M.op x y)) = (σ (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21140 eq300351
    | exact resolve eq300351 eq21140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21140 eq300351
  have eq540315 : (k (M.op x y) (M.op x y)) = (σ (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq539997
  have eq540372 : (M.op x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17893 eq540315
    | exact resolve eq540315 eq17893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540315
  have eq1872370 : (k x (M.op x y)) = (k x (M.op (M.op x y) (M.op x y))) ∨ x = (σ x) ∨ x = (M.op y x) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20776 eq58351
    | exact resolve eq58351 eq20776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20776 eq58351
  have eq1872428 : (k x (M.op x y)) = (k x (M.op (M.op x y) (M.op x y))) ∨ x = (σ x) ∨ x = (M.op y x) := by grind
  clear eq1872370
  have eq1877817 : (k x (M.op x y)) = (k x (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq540372 eq58444
    | exact resolve eq58444 eq540372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58444 eq540372
  have eq1877867 : (k x (M.op x y)) = (k x (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1877817
  have eq1938785 : ∀ X0 : G, (k x (M.op x y)) = (k x (M.op X0 (M.op x y))) ∨ x = (σ x) ∨ x = (M.op y x) ∨ x = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq294219 eq1872428
    | exact resolve eq1872428 eq294219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294219 eq1872428
  have eq1938839 : ∀ X0 : G, (k x (M.op x y)) = (k x (M.op X0 (M.op x y))) ∨ x = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1938785 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938785
  have eq1970768 : (k x (M.op x y)) = (M.op x x) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1877867 eq518
    | (have j0 := eq518 x
       grind)
    | exact resolve eq518 eq1877867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877867
  have eq1970862 : (k x (M.op x y)) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1970768
       have r₂ := eq278732
       grind)
    | exact resolve eq1970768 eq278732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278732 eq1970768
  have eq1970977 : (k (σ x) (σ (M.op x y))) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1970862 eq46
    | exact resolve eq46 eq1970862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970862
  have eq1971143 : (σ (M.op x x)) = (k (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq95516 eq1970977
    | exact resolve eq1970977 eq95516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970977
  have eq1973856 : (σ y) = (k (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1971143
       have i₂ := eq19814
       grind)
    | exact superpose eq19814 eq1971143
    | exact resolve eq1971143 eq19814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19814 eq1971143
  have eq1974432 : (σ y) = (k (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1973856
  have eq1974475 : (σ y) = (k (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1974432
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1974432
    | exact resolve eq1974432 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974432
  have eq1994303 : (k x (M.op x y)) = (M.op x x) ∨ x = (M.op x (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1938839 eq518
    | (have j0 := eq518 x
       grind)
    | exact resolve eq518 eq1938839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq1938839
  have eq1994433 : (k x (M.op x y)) = (M.op x x) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1994303
       have r₂ := eq278644
       grind)
    | exact resolve eq1994303 eq278644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278644 eq1994303
  have eq1994536 : (k (σ x) (σ (M.op x y))) = (σ (M.op x x)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1994433 eq46
    | exact resolve eq46 eq1994433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq1994433
  have eq1994705 : (σ (M.op x x)) = (k (σ x) (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq95516 eq1994536
    | exact resolve eq1994536 eq95516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994536
  have eq1997417 : (σ y) = (k (σ x) (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1994705
       have i₂ := eq19813
       grind)
    | exact superpose eq19813 eq1994705
    | exact resolve eq1994705 eq19813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19813 eq1994705
  have eq1997995 : (σ y) = (k (σ x) (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by grind
  clear eq1997417
  have eq1998038 : (σ y) = (k (σ x) (M.op x y)) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1997995
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1997995
    | exact resolve eq1997995 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1997995
  have eq3771646 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (σ x) ∨ x = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19911 eq1998038
    | (have j1 := eq19911 (σ x)
       grind)
    | exact resolve eq1998038 eq19911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19911 eq1998038
  have eq3771823 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (σ x) := by grind
  clear eq3771646
  have eq3775785 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (σ x) := by grind
  clear eq3771823
  have eq3775826 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq27 eq3775785
    | exact resolve eq3775785 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775785
  have eq3775863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op y x) ∨ x = (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq3775826 eq19877
    | exact resolve eq19877 eq3775826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19877 eq3775826
  have eq3775965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (σ x) := by grind
  clear eq3775863
  have eq3775977 : x = (M.op y x) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq3775965
       have r₂ := eq28
       grind)
    | exact resolve eq3775965 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775965
  have eq3778507 : (M.op (M.op x y) y) = (M.op y x) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq3775977
       grind)
    | exact superpose eq3775977 eq56
    | exact resolve eq56 eq3775977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3778525 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq215 eq3778507
    | exact resolve eq3778507 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778507
  have eq3781531 : x = (M.op x (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq3775977
       have i₂ := eq3778525
       grind)
    | exact superpose eq3778525 eq3775977
    | exact resolve eq3775977 eq3778525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775977 eq3778525
  have eq3781554 : x = (M.op x (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by grind
  clear eq3781531
  have eq3781665 : x = (σ x) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq3781554 eq17893
    | exact resolve eq17893 eq3781554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17893 eq3781554
  have eq3782125 : x = (σ x) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq3781665
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3781665
    | exact resolve eq3781665 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3781665
  have eq3782126 : (M.op x y) = (σ x) ∨ x = (σ x) := by grind
  clear eq3782125
  have eq3782207 : x = (τ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq3782126 eq29
    | exact resolve eq29 eq3782126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq3782969 : x ≠ (M.op x y) ∨ x = (σ x) := by grind
  clear eq3782126
  have eq3783489 : x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq95518 eq3782207
    | exact resolve eq3782207 eq95518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95518 eq3782207
  have eq3786023 : x = (σ x) := by
    first
    | (have r₁ := eq3783489
       have r₂ := eq3782969
       grind)
    | exact resolve eq3783489 eq3782969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782969 eq3783489
  have eq3786026 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq3786023 eq27
    | exact resolve eq27 eq3786023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3786038 : (k x (M.op x y)) = (τ (k x (σ (M.op x y)))) := by
    first
    | exact superpose eq3786023 eq66
    | exact resolve eq66 eq3786023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq3786720 : (σ y) = (k x (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3786023 eq1974475
    | exact resolve eq1974475 eq3786023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974475 eq3786023
  have eq3786789 : (k x (M.op x y)) = (τ (k x (M.op x y))) := by
    first
    | exact superpose eq95516 eq3786038
    | exact resolve eq3786038 eq95516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3786038
  have eq3957928 : (σ y) = (τ (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3786720 eq3786789
    | exact resolve eq3786789 eq3786720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3786720 eq3786789
  have eq3958030 : x = (M.op y x) ∨ x = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq3957928
    | exact resolve eq3957928 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3957928
  have eq3958616 : (M.op (M.op x y) y) = (M.op y x) ∨ x = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq3958030
       grind)
    | exact superpose eq3958030 eq56
    | exact resolve eq56 eq3958030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq3958631 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq215 eq3958616
    | exact resolve eq3958616 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq3958616
  have eq4001225 : x = (M.op x (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq3958030
       have i₂ := eq3958631
       grind)
    | exact superpose eq3958631 eq3958030
    | exact resolve eq3958030 eq3958631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3958030 eq3958631
  have eq4001254 : x = (M.op x (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq4001225
  have eq4004549 : x = (M.op x (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq4001254 eq236
    | exact resolve eq236 eq4001254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq4001254
  have eq4004997 : x = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq3786026 eq4004549
    | exact resolve eq4004549 eq3786026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004549
  have eq4004998 : y = (σ y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq4004997
  have eq4005809 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4004998 eq3786026
    | exact resolve eq3786026 eq4004998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004998
  have eq4005843 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4005809
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4005809
    | exact resolve eq4005809 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4005809
  have eq4006239 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4005843 eq28
    | exact resolve eq28 eq4005843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4005843
  have eq4006322 : x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4006239
       have r₂ := eq95516
       grind)
    | exact resolve eq4006239 eq95516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4006239
  have eq4006328 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq4006322 eq28
    | exact resolve eq28 eq4006322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4006330 : (M.op x (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq4006322 eq230
    | exact resolve eq230 eq4006322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq4006400 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq3786026 eq4006330
    | exact resolve eq4006330 eq3786026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3786026 eq4006330
  have eq4006402 : x ≠ (M.op x y) := by
    first
    | exact superpose eq95516 eq4006328
    | exact resolve eq4006328 eq95516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95516 eq4006328
  have eq4006403 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq4006322 eq4006400
    | exact resolve eq4006400 eq4006322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4006322 eq4006400
  have eq4006465 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq4006403 eq524
    | exact resolve eq524 eq4006403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq4006403
  have eq4008699 : x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq4006465 y
       grind)
    | exact superpose eq4006465 eq19
    | (have j1 := eq4006465 y
       grind)
    | exact resolve eq19 eq4006465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4006465
  have eq4009288 : False := by grind
  exact eq4009288

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxx_pxy_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq178 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq178 x x X2 X3 X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq185 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq182 x x X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq182
    | exact resolve eq182 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq192 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq179 x x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq180
  have eq238 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq214 eq185
    | exact resolve eq185 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq214
  have eq1237 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1239 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1413 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1417 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1413 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1413 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1413 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1483 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq192 X0 X0
       have i₂ := eq1417 X0
       grind)
    | exact superpose eq1417 eq192
    | exact resolve eq192 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1537 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1483 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1483
    | exact resolve eq1483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6042 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1237
       grind)
    | exact superpose eq1237 eq39
    | exact resolve eq39 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq6043 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6042
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6042
    | exact resolve eq6042 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6042
  have eq6045 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq6043
    | exact resolve eq6043 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6043
  have eq6047 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq6045
       have i₂ := eq1417 x
       grind)
    | exact superpose eq1417 eq6045
    | exact resolve eq6045 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6045
  have eq30436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq6047 eq1239
    | exact resolve eq1239 eq6047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30443 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq30436
       have r₂ := eq27
       grind)
    | exact resolve eq30436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30436
  have eq30449 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq30443
       have i₂ := eq1417 sF2
       grind)
    | exact superpose eq1417 eq30443
    | exact resolve eq30443 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30443
  have eq30453 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq30449 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq30449
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq30449
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq30449
       grind)
    | exact resolve eq12 eq30449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30449
  have eq30482 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq30453
       have r₂ := eq26
       grind)
    | exact resolve eq30453 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30453
  have eq30490 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq30482
       have i₂ := eq1417 sF2
       grind)
    | exact superpose eq1417 eq30482
    | exact resolve eq30482 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30482
  have eq30491 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq30490
  have eq30493 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq6047 eq30491
    | exact resolve eq30491 eq6047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6047 eq30491
  have eq30494 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq30493
       have r₂ := eq27
       grind)
    | exact resolve eq30493 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30493
  have eq30500 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq30494 eq141
    | exact resolve eq141 eq30494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30494
  have eq30524 : x = (k x x) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq29 eq30500
    | exact resolve eq30500 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30500
  have eq30525 : (M.op x y) = (M.op y x) ∨ x = (k x x) := by grind
  clear eq30524
  have eq30545 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq30525
       grind)
    | exact superpose eq30525 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq30525
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq30525
       grind)
    | exact resolve eq12 eq30525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30525
  have eq30576 : x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have r₁ := eq30545
       have r₂ := eq18
       grind)
    | exact resolve eq30545 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30545
  have eq30585 : x = (k x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq30576
       have i₂ := eq1417 x
       grind)
    | exact superpose eq1417 eq30576
    | exact resolve eq30576 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30576
  have eq30586 : (M.op x y) = (k y x) ∨ x = (k x x) := by grind
  clear eq30585
  have eq30593 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq30586
       grind)
    | exact superpose eq30586 eq39
    | exact resolve eq39 eq30586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30586
  have eq30594 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq30593
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30593
    | exact resolve eq30593 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq30593
  have eq30598 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq30594
    | exact resolve eq30594 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30594
  have eq30603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq30598 eq1239
    | exact resolve eq1239 eq30598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq30610 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq30603
       have r₂ := eq27
       grind)
    | exact resolve eq30603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30603
  have eq30616 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq30610
       have i₂ := eq1417 sF2
       grind)
    | exact superpose eq1417 eq30610
    | exact resolve eq30610 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30610
  have eq31975 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq30616 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq30616
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq30616
       grind)
    | exact resolve eq12 eq30616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30616
  have eq32006 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq31975
       have r₂ := eq26
       grind)
    | exact resolve eq31975 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31975
  have eq32018 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq32006
       have i₂ := eq1417 sF2
       grind)
    | exact superpose eq1417 eq32006
    | exact resolve eq32006 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32006
  have eq32019 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by grind
  clear eq32018
  have eq32026 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq30598 eq32019
    | exact resolve eq32019 eq30598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30598 eq32019
  have eq32027 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq32026
       have r₂ := eq27
       grind)
    | exact resolve eq32026 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32026
  have eq32033 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) := by
    first
    | exact superpose eq32027 eq141
    | exact resolve eq141 eq32027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq32027
  have eq32057 : x = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq32033
    | exact resolve eq32033 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32033
  have eq32058 : x = (k x x) := by grind
  clear eq32057
  have eq32080 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq32058
       grind)
    | exact superpose eq32058 eq39
    | exact resolve eq39 eq32058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32082 : (M.op (M.op x y) y) = (M.op x x) := by
    first
    | (have i₁ := eq1483 x
       have i₂ := eq32058
       grind)
    | exact superpose eq32058 eq1483
    | exact resolve eq1483 eq32058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq32086 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1537 x
       have i₂ := eq32058
       grind)
    | exact superpose eq32058 eq1537
    | exact resolve eq1537 eq32058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq32098 : (M.op (M.op x y) y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq32086
       have i₂ := eq1417 (σ x)
       grind)
    | exact superpose eq1417 eq32086
    | exact resolve eq32086 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32086
  have eq32101 : (k x x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq32082
       have i₂ := eq1417 x
       grind)
    | exact superpose eq1417 eq32082
    | exact resolve eq32082 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417 eq32082
  have eq32103 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq32080
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32080
    | exact resolve eq32080 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32080
  have eq32113 : (σ (k x x)) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq32098
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq32098
    | exact resolve eq32098 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32098
  have eq32116 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq32101
       have i₂ := eq32058
       grind)
    | exact superpose eq32058 eq32101
    | exact resolve eq32101 eq32058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32058 eq32101
  have eq32123 : (k (σ x) (σ x)) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq32113
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq32113
    | exact resolve eq32113 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq32113
  have eq32131 : x = (k (σ x) (σ x)) := by
    first
    | exact superpose eq32116 eq32123
    | exact resolve eq32123 eq32116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32123
  have eq32138 : x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq32131
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32131
    | exact resolve eq32131 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32131
  have eq32144 : x = (σ x) := by
    first
    | exact superpose eq32103 eq32138
    | exact resolve eq32138 eq32103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32103 eq32138
  have eq32900 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq32116 eq238
    | exact resolve eq238 eq32116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq32982 : x = (M.op x y) := by
    first
    | exact superpose eq32116 eq192
    | exact resolve eq192 eq32116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq32116
  have eq32991 : x = (M.op x y) := by
    first
    | (have i₁ := eq32982
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32982
    | exact resolve eq32982 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq32982
  have eq33066 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq32900 X0
       have i₂ := eq32144
       grind)
    | exact superpose eq32144 eq32900
    | exact resolve eq32900 eq32144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32900
  have eq33144 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq32991
       grind)
    | exact superpose eq32991 eq22
    | exact resolve eq22 eq32991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq33184 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq32144
       have i₂ := eq32991
       grind)
    | exact superpose eq32991 eq32144
    | exact resolve eq32144 eq32991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32144 eq32991
  have eq33206 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq33184 eq33144
    | exact resolve eq33144 eq33184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33144
  have eq33569 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq33206 eq20
    | exact resolve eq20 eq33206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq33206
  have eq34115 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33066 eq26
    | (have j1 := eq33066 (σ y)
       grind)
    | exact resolve eq26 eq33066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq33066
  have eq34184 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33184 eq34115
    | exact resolve eq34115 eq33184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33184 eq34115
  have eq34215 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq34184 eq27
    | exact resolve eq27 eq34184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq34184
  have eq34230 : False := by grind
  exact eq34230

/-- `Equation4452`: `x ◇ (y ◇ x) = (z ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_pxx_pxy_Equation4452 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) X0) := by
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
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq175 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X0) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 (M.op x X0) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 x X3
       have i₂ := eq16 X1 x X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ x)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq739 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq181
    | exact resolve eq181 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq924 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq862 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq862 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq862 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq862 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq1451 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 (M.op X2 X0)) ∨ (k (M.op X0 (M.op X2 X0)) X0) = (M.op X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X2 X0)) X0
       have i₂ := eq178 X0 X2 X1
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 (M.op X0 (M.op X2 X0)) X0
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X2 X0)) X0
       have r₂ := eq178 X0 X2 X2
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1476 : ∀ X0 X2 : G, (k (M.op X0 (M.op X2 X0)) X0) = (M.op X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq1451 X0 x X2
       grind)
    | (have r₁ := eq1451 X0 x X2
       have r₂ := eq181 X0 x X2
       grind)
    | (have r₁ := eq1451 X0 X2 x
       have r₂ := eq181 X0 x X2
       grind)
    | exact resolve eq1451 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq1515 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq853
       grind)
    | exact superpose eq853 eq40
    | exact resolve eq40 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq1516 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1515
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1515
    | exact resolve eq1515 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq1518 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1516
    | exact resolve eq1516 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq1811 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq179 x
       have i₂ := eq739 y X0 x
       grind)
    | exact superpose eq739 eq179
    | exact resolve eq179 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1818 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op y (M.op X0 y)) y) := by
    intro X0
    first
    | (have i₁ := eq1811 X0
       have i₂ := eq1476 y X0
       grind)
    | exact superpose eq1476 eq1811
    | exact resolve eq1811 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476 eq1811
  have eq1860 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) y) := by
    first
    | (have i₁ := eq1818 x
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq1818
    | exact resolve eq1818 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1818
  have eq1884 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (σ y)) := by
    first
    | exact superpose eq1860 eq40
    | exact resolve eq40 eq1860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1860
  have eq1903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1518 eq857
    | exact resolve eq857 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1910 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1903
       have r₂ := eq27
       grind)
    | exact resolve eq1903 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq1918 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1910 eq175
    | exact resolve eq175 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1920 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1910 eq176
    | exact resolve eq176 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1921 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1910 eq178
    | exact resolve eq178 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1923 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1910 eq181
    | exact resolve eq181 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1925 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1910 eq739
    | exact resolve eq739 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1928 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1925
    | (have j0 := eq1925 X0
       grind)
    | exact resolve eq1925 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq1930 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1923
    | (have j0 := eq1923 X0
       grind)
    | exact resolve eq1923 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq1932 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1921
    | (have j0 := eq1921 X0
       grind)
    | exact resolve eq1921 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1933 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1910 eq1920
    | exact resolve eq1920 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910 eq1920
  have eq1935 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1918
    | (have j0 := eq1918 X0
       grind)
    | exact resolve eq1918 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918
  have eq1940 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1930 eq1932
    | exact resolve eq1932 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930 eq1932
  have eq1941 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1933 eq1935
    | exact resolve eq1935 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933 eq1935
  have eq1950 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1940 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq1940
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1940
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1940
       grind)
    | exact resolve eq13 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1959 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1940 eq739
    | exact resolve eq739 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq1940
  have eq1960 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1950
  have eq1962 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1928 eq1959
    | exact resolve eq1959 eq1928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928 eq1959
  have eq1967 : (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1941 eq1960
    | exact resolve eq1960 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq1969 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1941 eq1962
    | exact resolve eq1962 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941 eq1962
  have eq1974 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1969
    | exact resolve eq1969 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq2234 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1967 eq141
    | exact resolve eq141 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1967
  have eq2237 : y = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2234
    | exact resolve eq2234 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2234
  have eq2239 : y = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1974 eq2237
    | exact resolve eq2237 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974 eq2237
  have eq2240 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2239
    | exact resolve eq2239 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2239
  have eq2582 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq905 y x
       have i₂ := eq2240
       grind)
    | exact superpose eq2240 eq905
    | (have j0 := eq905 y x
       grind)
    | (have r₁ := eq905 y x
       have r₂ := eq2240
       grind)
    | exact resolve eq905 eq2240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq2240
  have eq2583 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2582
  have eq2584 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2583
  have eq2587 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2584
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2584
    | exact resolve eq2584 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2584
  have eq2588 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2587
  have eq2595 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2588
       grind)
    | exact superpose eq2588 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2588
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2588
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2588
       grind)
    | exact resolve eq13 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2596 : ∀ X0 : G, (M.op y x) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq2588
       grind)
    | exact superpose eq2588 eq16
    | exact resolve eq16 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2602 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181 x X0 y
       have i₂ := eq2588
       grind)
    | exact superpose eq2588 eq181
    | exact resolve eq181 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2605 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2595
  have eq2611 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2602 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2602
    | (have j0 := eq2602 X0
       grind)
    | exact resolve eq2602 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602
  have eq2617 : ∀ X0 : G, y = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2588 eq2596
    | exact resolve eq2596 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2588 eq2596
  have eq2618 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2605
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2605
    | exact resolve eq2605 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2605
  have eq2624 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2611 eq2617
    | exact resolve eq2617 eq2611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611 eq2617
  have eq2626 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2624 eq27
    | exact resolve eq27 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2627 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2624 eq185
    | (have r₁ := eq185
       have r₂ := eq2624
       grind)
    | exact resolve eq185 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2628 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2624 eq196
    | exact resolve eq196 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2639 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2627
  have eq2641 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2628
    | exact resolve eq2628 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq2642 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2624 eq2641
    | exact resolve eq2641 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2624 eq2641
  have eq2646 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq2618
       grind)
    | exact superpose eq2618 eq39
    | exact resolve eq39 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2618
  have eq2650 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2646
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2646
    | exact resolve eq2646 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2652 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2650
    | exact resolve eq2650 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650
  have eq2881 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2652 eq924
    | (have j0 := eq924 (σ y) (σ x)
       grind)
    | exact resolve eq924 eq2652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924 eq2652
  have eq2897 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2881
    | exact resolve eq2881 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2881
  have eq2900 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2897
       have r₂ := eq27
       grind)
    | exact resolve eq2897 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2897
  have eq2903 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2900
    | exact resolve eq2900 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2900
  have eq2904 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2903
  have eq3291 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2639 eq2642
    | exact resolve eq2642 eq2639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639 eq2642
  have eq3307 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3291
  have eq3335 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3307 eq1518
    | exact resolve eq1518 eq3307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3307
  have eq3345 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3335
  have eq3352 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3345
       have r₂ := eq2626
       grind)
    | exact resolve eq3345 eq2626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626 eq3345
  have eq3375 : ∀ X0 : G, (M.op y x) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq3352
       grind)
    | exact superpose eq3352 eq16
    | exact resolve eq16 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3381 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 x X0 y
       have i₂ := eq3352
       grind)
    | exact superpose eq3352 eq181
    | exact resolve eq181 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3394 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3381 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3381
    | (have j0 := eq3381 X0
       grind)
    | exact resolve eq3381 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381
  have eq3400 : ∀ X0 : G, y = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3352 eq3375
    | exact resolve eq3375 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352 eq3375
  have eq3408 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3394 eq3400
    | exact resolve eq3400 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3394 eq3400
  have eq3409 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3408
  have eq3412 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3409
       grind)
    | exact superpose eq3409 eq18
    | exact resolve eq18 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3413 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3409
       grind)
    | exact superpose eq3409 eq24
    | exact resolve eq24 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3445 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3413
    | exact resolve eq3413 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3413
  have eq3464 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3445 eq2904
    | (have r₁ := eq2904
       have r₂ := eq3445
       grind)
    | exact resolve eq2904 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904 eq3445
  have eq3465 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3464
  have eq3466 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3465
  have eq3487 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3466 eq27
    | exact resolve eq27 eq3466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3488 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3466 eq185
    | (have r₁ := eq185
       have r₂ := eq3466
       grind)
    | exact resolve eq185 eq3466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq3489 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3466 eq196
    | exact resolve eq196 eq3466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq3500 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3488
  have eq3503 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3489
    | exact resolve eq3489 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3489
  have eq3505 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3466 eq3503
    | exact resolve eq3503 eq3466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3466 eq3503
  have eq3623 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3500 eq3505
    | exact resolve eq3505 eq3500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3500 eq3505
  have eq3641 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3623
  have eq3671 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3641 eq1518
    | exact resolve eq1518 eq3641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq3675 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3641 eq152
    | exact resolve eq152 eq3641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq3641
  have eq3681 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq3671
  have eq3685 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3675
    | exact resolve eq3675 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3675
  have eq3688 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3681
       have r₂ := eq3487
       grind)
    | exact resolve eq3681 eq3487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3487 eq3681
  have eq3690 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3409 eq3685
    | exact resolve eq3685 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685
  have eq3693 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3409 eq3688
    | exact resolve eq3688 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409 eq3688
  have eq3712 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (k x (M.op x y)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3693 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq3693
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3693
       grind)
    | exact resolve eq12 eq3693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3720 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3693 eq181
    | exact resolve eq181 eq3693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693
  have eq3725 : x = (M.op x (M.op x y)) ∨ (k x (M.op x y)) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq3712
  have eq3733 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3412 eq3720
    | exact resolve eq3720 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq3741 : x = (M.op x y) ∨ (k x (M.op x y)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3412 eq3725
    | exact resolve eq3725 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412 eq3725
  have eq3742 : x = (M.op x y) ∨ (k x (M.op x y)) = (M.op x x) := by grind
  clear eq3741
  have eq3748 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3690 eq3742
    | exact resolve eq3742 eq3690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690 eq3742
  have eq3776 : ∀ X0 : G, (M.op x x) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 x X0 x
       have i₂ := eq3748
       grind)
    | exact superpose eq3748 eq181
    | exact resolve eq181 eq3748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3791 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3733 eq3776
    | exact resolve eq3776 eq3733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3733 eq3776
  have eq3842 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3748
       have i₂ := eq3791
       grind)
    | exact superpose eq3791 eq3748
    | exact resolve eq3748 eq3791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748 eq3791
  have eq3870 : x = (M.op x y) := by grind
  clear eq3842
  have eq3885 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3870
       grind)
    | exact superpose eq3870 eq18
    | exact resolve eq18 eq3870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3886 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq3870
       grind)
    | exact superpose eq3870 eq22
    | exact resolve eq22 eq3870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3870
  have eq3894 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3886 eq20
    | exact resolve eq20 eq3886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3886
  have eq4548 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3885 eq1884
    | exact resolve eq1884 eq3885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884 eq3885
  have eq4577 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq4548
    | exact resolve eq4548 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4548
  have eq4580 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3894 eq4577
    | exact resolve eq4577 eq3894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4577
  have eq4625 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4580 eq857
    | exact resolve eq857 eq4580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq4633 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4625
  have eq4730 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4633 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4633
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4633
       grind)
    | exact resolve eq12 eq4633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4741 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4633 eq181
    | exact resolve eq181 eq4633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4633
  have eq4746 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4730
  have eq4750 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq4741
    | (have j0 := eq4741 X0
       grind)
    | exact resolve eq4741 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741
  have eq4761 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4746
    | exact resolve eq4746 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4746
  have eq4762 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq4761
  have eq4769 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4580 eq4762
    | exact resolve eq4762 eq4580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4580 eq4762
  have eq4942 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4769 eq181
    | exact resolve eq181 eq4769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq4951 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4750 eq4942
    | exact resolve eq4942 eq4750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4750 eq4942
  have eq4958 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4769 eq4951
    | exact resolve eq4951 eq4769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4769 eq4951
  have eq4959 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4958
  have eq4970 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4959 eq27
    | exact resolve eq27 eq4959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4959
  have eq4991 : False := by grind
  exact eq4991

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyy_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 (k X1 X1) X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq39 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq40 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq43
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq47 X1 X0
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq47 X0 (M.op X1 X1)
       have r₂ := eq41 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq47 X1 X1
       have r₂ := eq41 (k X1 X1) X1
       grind)
    | exact resolve eq47 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq47
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq49 X0 X1
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq49 X0 X1
       grind)
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq50
  have eq130 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq134 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq130 X0 X1
       have j1 := eq53 X0 X1
       grind)
    | (have r₁ := eq130 X0 X1
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq130 X0 X0
       have r₂ := eq53 X0 X0
       grind)
    | exact resolve eq130 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq130
  have eq257 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq134 (σ X0) (σ X1)
       grind)
    | exact superpose eq134 eq15
    | exact resolve eq15 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq257 X0 X1
       have i₂ := eq134 X0 X1
       grind)
    | exact superpose eq134 eq257
    | exact resolve eq257 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq257
  have eq267 : False := by grind
  exact eq267

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq12
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq21 X0
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq31 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq38
    | exact resolve eq38 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq71 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
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
  have eq84 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq165 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq69
    | exact resolve eq69 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ x)
       have i₂ := eq69 x x
       grind)
    | exact superpose eq69 eq21
    | (have j1 := eq69 X0 X0
       grind)
    | exact resolve eq21 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq69
  have eq184 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq390 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq184 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq184
    | exact resolve eq184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq403 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq390 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq390
    | (have j0 := eq390 X0
       grind)
    | exact resolve eq390 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq390
  have eq407 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq403 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq403
    | (have j0 := eq403 X0
       grind)
    | exact resolve eq403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq427 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (k X0 X0) X0
       have i₂ := eq407 X0
       grind)
    | exact superpose eq407 eq12
    | (have j1 := eq407 X0
       grind)
    | (have r₁ := eq12 (k X0 X0) X0
       have r₂ := eq407 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq407 X0
       grind)
    | exact resolve eq12 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq428 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq438 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq428 X0
       grind)
    | exact superpose eq428 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq428 X0
       grind)
    | exact resolve eq14 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq443 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq438 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq450 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq443 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq443 x
       have r₂ := eq12 (k x x) x
       grind)
    | (have r₁ := eq443 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq443 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq903 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 (M.op (τ X0) X1) X2
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq38
    | (have j1 := eq71 X0 X1
       grind)
    | exact resolve eq38 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq71
  have eq918 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq903 X0 X1 X2
       have i₂ := eq55 X0 X1 X2
       grind)
    | exact superpose eq55 eq903
    | (have j0 := eq903 X0 X1 X2
       grind)
    | exact resolve eq903 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq903
  have eq1060 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 (k X0 X0) X0
       have i₂ := eq450 X0
       grind)
    | exact superpose eq450 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq450 X0
       grind)
    | (have r₁ := eq12 (k X0 X0) X0
       have r₂ := eq450 X0
       grind)
    | exact resolve eq12 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq1079 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1060 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1114 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq105 x X2 X0 X1
       grind)
    | exact superpose eq105 eq31
    | exact resolve eq31 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1115 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq105 x X2 X0 X1
       grind)
    | exact superpose eq105 eq9
    | exact resolve eq9 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1195 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1115 x X1 X0
       grind)
    | exact superpose eq1115 eq9
    | exact resolve eq9 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1200 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq1115 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1115 eq9
    | exact resolve eq9 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1114 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq1115 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1115 eq1114
    | exact resolve eq1114 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq6017 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1115 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1200 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1200 eq1115
    | exact resolve eq1115 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq1200
  have eq6095 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq84 (M.op X0 (M.op X1 X2)) X2 X2
       have i₂ := eq6017 X0 X1 X2
       grind)
    | exact superpose eq6017 eq84
    | exact resolve eq84 eq6017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq6017
  have eq6604 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ X0)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op X2 (M.op X3 (τ X0))))
       have i₂ := eq6095 (τ X0) X2 X3 X1
       grind)
    | exact superpose eq6095 eq18
    | exact resolve eq18 eq6095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6617 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6604 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6604
    | exact resolve eq6604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6604
  have eq22934 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1079 (τ X0)
       have i₂ := eq918 X0 (τ X0) X0
       grind)
    | exact superpose eq918 eq1079
    | (have j0 := eq1079 (τ X0)
       have j1 := eq918 X0 (τ X0) x
       grind)
    | exact resolve eq1079 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq1079
  have eq22992 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq22934 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22934
  have eq23048 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq22992 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq22992 X0
       have r₂ := eq12 (τ X0) (τ X0)
       grind)
    | exact resolve eq22992 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22992
  have eq23097 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23048 X0
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq23048
    | (have j0 := eq23048 X0
       grind)
    | exact resolve eq23048 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23048
  have eq23125 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23097 X0
       have i₂ := eq30 (τ X0)
       grind)
    | exact superpose eq30 eq23097
    | (have j0 := eq23097 X0
       grind)
    | exact resolve eq23097 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq23097
  have eq23135 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23125 X0
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq23125
    | (have j0 := eq23125 X0
       grind)
    | exact resolve eq23125 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq23125
  have eq23136 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq23135 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23135
  have eq23145 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23136 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23136
    | exact resolve eq23136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23186 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (τ (k X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6617 X0 X1 X2 (τ X0)
       have i₂ := eq23136 X0
       grind)
    | exact superpose eq23136 eq6617
    | exact resolve eq6617 eq23136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6617
  have eq23245 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) (M.op X1 (M.op X2 (τ (k X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6095 (τ X0) X2 (τ X0) X1
       have i₂ := eq23136 X0
       grind)
    | exact superpose eq23136 eq6095
    | exact resolve eq6095 eq23136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6095
  have eq23303 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq23145 X0
       have i₂ := eq27 (σ X0) X0
       grind)
    | exact superpose eq27 eq23145
    | exact resolve eq23145 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23145
  have eq23322 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23303 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23303
    | exact resolve eq23303 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23303
  have eq23442 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23322 (σ X0)
       grind)
    | exact superpose eq23322 eq15
    | exact resolve eq15 eq23322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23501 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23442 X0
       have i₂ := eq23322 X0
       grind)
    | exact superpose eq23322 eq23442
    | exact resolve eq23442 eq23322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23442
  have eq24146 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1195 (σ X0) (σ X0)
       have i₂ := eq23501 X0
       grind)
    | exact superpose eq23501 eq1195
    | exact resolve eq1195 eq23501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26419 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ X3)) = X0 ∨ (M.op (σ X3) (σ X3)) = X0 ∨ (M.op X0 (σ X3)) = (σ (k (k (τ X0) (M.op X1 (M.op X2 (τ (k X0 X0))))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq165 X0 (M.op X1 (M.op X2 (τ (k X0 X0)))) X2
       have i₂ := eq23186 X0 X1 X2
       grind)
    | exact superpose eq23186 eq165
    | exact resolve eq165 eq23186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq23186
  have eq26508 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = X0 ∨ (M.op X0 (σ X3)) = X0 ∨ (M.op X0 (σ X3)) = (σ (k (k (τ X0) (M.op X1 (M.op X2 (τ (k X0 X0))))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26419 X0 X1 X2 X3
       have i₂ := eq23501 X3
       grind)
    | exact superpose eq23501 eq26419
    | (have j0 := eq26419 X0 X1 X2 X3
       grind)
    | exact resolve eq26419 eq23501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23501 eq26419
  have eq26585 : ∀ X0 X3 : G, (σ (k (τ X0) X3)) = (M.op X0 (σ X3)) ∨ (σ (M.op X3 X3)) = X0 ∨ (M.op X0 (σ X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq26508 X0 x x X3
       have i₂ := eq23245 X0 x x
       grind)
    | exact superpose eq23245 eq26508
    | (have j0 := eq26508 X0 x x X3
       grind)
    | exact resolve eq26508 eq23245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23245 eq26508
  have eq26646 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (σ (M.op X3 X3)) = X0 ∨ (M.op X0 (σ X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq26585 X0 X3
       have i₂ := eq18 X0 X3
       grind)
    | exact superpose eq18 eq26585
    | (have j0 := eq26585 X0 X3
       grind)
    | exact resolve eq26585 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26585
  have eq26695 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (σ (M.op X3 X3)) = X0 := by
    intro X0 X3
    first
    | (have j0 := eq26646 X0 X3
       have j1 := eq12 X0 (σ X3)
       grind)
    | (have r₁ := eq26646 (M.op (σ (M.op X3 X3)) x) X3
       have r₂ := eq12 (σ (M.op X3 X3)) x
       grind)
    | (have r₁ := eq26646 X0 X3
       have r₂ := eq12 X0 (σ X3)
       grind)
    | exact resolve eq26646 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26646
  have eq31328 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26695 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26695
    | (have j0 := eq26695 X1 (τ X0)
       grind)
    | exact resolve eq26695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31490 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq26695 (σ X0) X1
       grind)
    | exact superpose eq26695 eq15
    | (have j1 := eq26695 (σ X0) X1
       grind)
    | exact resolve eq15 eq26695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26695
  have eq31637 : ∀ X0 X1 : G, (σ (τ (k X0 X0))) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31328 X0 X1
       have i₂ := eq23136 X0
       grind)
    | exact superpose eq23136 eq31328
    | (have j0 := eq31328 X0 X1
       grind)
    | exact resolve eq31328 eq23136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23136 eq31328
  have eq31687 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31637 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq31637
    | (have j0 := eq31637 X0 X1
       grind)
    | exact resolve eq31637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31637
  have eq31705 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31687 X0 X1
       have i₂ := eq23322 X0
       grind)
    | exact superpose eq23322 eq31687
    | (have j0 := eq31687 X0 X1
       grind)
    | exact resolve eq31687 eq23322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23322 eq31687
  have eq31995 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq31705 X1 (τ X0)
       grind)
    | exact superpose eq31705 eq18
    | (have j1 := eq31705 X1 (τ X0)
       grind)
    | exact resolve eq18 eq31705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq31705
  have eq40047 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31995 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31995
    | exact resolve eq31995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31995
  have eq40339 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40047 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq40047
    | (have j0 := eq40047 X0 X1
       grind)
    | exact resolve eq40047 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40047
  have eq50425 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31490 x y
       grind)
    | exact superpose eq31490 eq16
    | (have j1 := eq31490 x y
       grind)
    | exact resolve eq16 eq31490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31490
  have eq51276 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50425
       have i₂ := eq40339 x y
       grind)
    | exact superpose eq40339 eq50425
    | (have j1 := eq40339 x y
       grind)
    | (have r₁ := eq50425
       have r₂ := eq40339 x y
       grind)
    | exact resolve eq50425 eq40339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40339
  have eq51279 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq51276
  have eq51350 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1195 y y
       have i₂ := eq51279
       grind)
    | exact superpose eq51279 eq1195
    | exact resolve eq1195 eq51279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51355 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1201 y y
       have i₂ := eq51279
       grind)
    | exact superpose eq51279 eq1201
    | exact resolve eq1201 eq51279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq51279
  have eq51934 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq50425
       have i₂ := eq51355
       grind)
    | exact superpose eq51355 eq50425
    | exact resolve eq50425 eq51355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50425 eq51355
  have eq51955 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq51934
  have eq52589 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq51955
       have i₂ := eq51350
       grind)
    | exact superpose eq51350 eq51955
    | exact resolve eq51955 eq51350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51350 eq51955
  have eq52592 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq52589
  have eq52593 : (σ x) = (σ (M.op y y)) := by grind
  clear eq52592
  have eq52604 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24146 y
       have i₂ := eq52593
       grind)
    | exact superpose eq52593 eq24146
    | exact resolve eq24146 eq52593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24146
  have eq52611 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq52593
       grind)
    | exact superpose eq52593 eq10
    | exact resolve eq10 eq52593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52593
  have eq52761 : x = (M.op y y) := by
    first
    | (have i₁ := eq52611
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52611
    | exact resolve eq52611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52611
  have eq53402 : x = (M.op x y) := by
    first
    | (have i₁ := eq1195 y y
       have i₂ := eq52761
       grind)
    | exact superpose eq52761 eq1195
    | exact resolve eq1195 eq52761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq52761
  have eq53553 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52604
       grind)
    | exact superpose eq52604 eq16
    | exact resolve eq16 eq52604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52604
  have eq53619 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq53553
       have i₂ := eq53402
       grind)
    | exact superpose eq53402 eq53553
    | exact resolve eq53553 eq53402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53402 eq53553
  have eq53620 : False := by grind
  exact eq53620

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq27 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
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
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq76 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X0 (M.op X1 (M.op X2 (M.op (σ X0) (σ X0))))
       have i₂ := eq69 (σ X0) X1 X2
       grind)
    | exact superpose eq69 eq29
    | exact resolve eq29 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq79 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq76
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq84 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq119 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op X2 (M.op (σ (σ X0)) (σ (σ X0)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X0 (τ (M.op X1 (M.op X2 (M.op (σ (σ X0)) (σ (σ X0))))))
       have i₂ := eq79 (σ X0) X1 X2
       grind)
    | exact superpose eq79 eq29
    | exact resolve eq29 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq124 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (M.op (σ (σ X0)) (σ (σ X0)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq119 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq119
    | exact resolve eq119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq137 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq222 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k X2 (τ X3)))) = (k (k (σ X0) X1) (k (σ X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27 X2 X3 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq27
    | exact resolve eq27 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq698 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq12
    | (have j1 := eq84 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq84 X0
       grind)
    | exact resolve eq12 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq84 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq714 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq712 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq715 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq714 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq714
    | (have j0 := eq714 X0
       grind)
    | exact resolve eq714 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq719 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq700 X0 X1
       have i₂ := eq222 X0 X1 X0 X1
       grind)
    | exact superpose eq222 eq700
    | (have j0 := eq700 X0 X1
       grind)
    | exact resolve eq700 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq721 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq698 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq698
    | (have j0 := eq698 X0
       grind)
    | exact resolve eq698 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq698
  have eq722 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq715 X0
       have j1 := eq713 X0
       grind)
    | (have r₁ := eq715 X0
       have r₂ := eq713 X0
       grind)
    | exact resolve eq715 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq715
  have eq724 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq719 X0 X1
       have j1 := eq12 (k (σ X0) X1) (k (σ X0) X1)
       grind)
    | (have r₁ := eq719 X0 X1
       have r₂ := eq12 (k (σ X0) X1) (k (σ X0) X1)
       grind)
    | exact resolve eq719 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq726 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq721 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq721
    | (have j0 := eq721 X0
       grind)
    | exact resolve eq721 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq727 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq726 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq726 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq726 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq810 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140 x y
       grind)
    | exact superpose eq140 eq16
    | (have j1 := eq140 x y
       grind)
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq827 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (σ (k (σ X0) (σ X0)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 X0 X1 X2
       have i₂ := eq722 (σ X0)
       grind)
    | exact superpose eq722 eq124
    | exact resolve eq124 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq845 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (k X0 X0)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq827 X0 X1 X2
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq827
    | exact resolve eq827 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq852 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq845 X0 X1 X2
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq845
    | exact resolve eq845 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq1274 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op (σ X0) (σ X0)))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op (σ X0) (σ X0))))))))
       have i₂ := eq852 (σ X0) X1 X2
       grind)
    | exact superpose eq852 eq29
    | exact resolve eq29 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq1285 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (k X0 X0)))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1274 X0 X1 X2
       have i₂ := eq722 X0
       grind)
    | exact superpose eq722 eq1274
    | exact resolve eq1274 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1297 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (M.op X0 X0)))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1285 X0 X1 X2
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq1285
    | exact resolve eq1285 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1307 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (M.op X0 X0)))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1297 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1297
    | exact resolve eq1297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq2072 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (σ (k X0 X0))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1307 (σ X0) X1 X2
       have i₂ := eq722 X0
       grind)
    | exact superpose eq722 eq1307
    | exact resolve eq1307 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2091 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (M.op (σ X0) (σ X0)))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X0 (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (M.op (σ X0) (σ X0))))))))))
       have i₂ := eq1307 (σ X0) X1 X2
       grind)
    | exact superpose eq1307 eq29
    | exact resolve eq29 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1307
  have eq2102 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (σ (k X0 X0)))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2091 X0 X1 X2
       have i₂ := eq722 X0
       grind)
    | exact superpose eq722 eq2091
    | exact resolve eq2091 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2112 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (σ (M.op X0 X0))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2072 X0 X1 X2
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq2072
    | exact resolve eq2072 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq2115 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (σ (M.op X0 X0)))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2102 X0 X1 X2
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq2102
    | exact resolve eq2102 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq2126 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (σ (M.op X0 X0)))))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2115 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2115
    | exact resolve eq2115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq4484 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq137
    | exact resolve eq137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq4556 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4484 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4484
    | (have j0 := eq4484 X0 X1
       grind)
    | exact resolve eq4484 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4484
  have eq4753 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq814 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq814
    | (have j0 := eq814 (τ X0) (τ X1)
       grind)
    | exact resolve eq814 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq4806 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4753 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4753
    | (have j0 := eq4753 X0 X1
       grind)
    | exact resolve eq4753 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4753
  have eq4836 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4806 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4806
    | (have j0 := eq4806 X0 X1
       grind)
    | exact resolve eq4806 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4806
  have eq4865 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4836 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4836
    | (have j0 := eq4836 X0 X1
       grind)
    | exact resolve eq4836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4836
  have eq4871 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4865 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4865
    | (have j0 := eq4865 X0 X1
       grind)
    | exact resolve eq4865 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4865
  have eq4877 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4871 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4871
    | (have j0 := eq4871 X0 X1
       grind)
    | exact resolve eq4871 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4871
  have eq4879 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4877 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4877
    | (have j0 := eq4877 X0 X1
       grind)
    | exact resolve eq4877 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4877
  have eq7677 : ∀ X0 X1 : G, (k (k (σ X0) X1) (k (σ X0) X1)) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 X1 X0 X1
       have i₂ := eq727 (k X0 (τ X1))
       grind)
    | exact superpose eq727 eq222
    | exact resolve eq222 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq7751 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7677 X0 X1
       have i₂ := eq724 X0 X1
       grind)
    | exact superpose eq724 eq7677
    | exact resolve eq7677 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq7677
  have eq12947 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (k (σ X0) (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (σ (M.op X0 X0))))))))))) (k (σ X0) (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (σ (M.op X0 X0)))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7751 X0 (τ (τ (τ (M.op X1 (M.op X2 (σ (σ (σ (σ (M.op X0 X0))))))))))
       have i₂ := eq2126 X0 X1 X2
       grind)
    | exact superpose eq2126 eq7751
    | exact resolve eq7751 eq2126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126 eq7751
  have eq13069 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12947 X0 x x
       have i₂ := eq2112 X0 x x
       grind)
    | exact superpose eq2112 eq12947
    | exact resolve eq12947 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112 eq12947
  have eq24963 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq810
       have i₂ := eq4556 y x
       grind)
    | exact superpose eq4556 eq810
    | (have j1 := eq4556 (σ x) (σ y)
       grind)
    | (have r₁ := eq810
       have r₂ := eq4556 y x
       grind)
    | (have r₁ := eq810
       have r₂ := eq4556 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq810
       have r₂ := eq4556 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq810 eq4556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq4556
  have eq24964 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq24963
  have eq24966 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24964
       grind)
    | exact superpose eq24964 eq16
    | exact resolve eq16 eq24964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24964
  have eq24967 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24966
       have r₂ := eq13069 x
       grind)
    | exact resolve eq24966 eq13069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24966
  have eq24970 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq24967
       grind)
    | exact superpose eq24967 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq24967
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq24967
       grind)
    | exact resolve eq12 eq24967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24967
  have eq24971 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq24970
  have eq24983 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq24971
       grind)
    | exact superpose eq24971 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq24971
       grind)
    | exact resolve eq12 eq24971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24971
  have eq24984 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq24983
  have eq24986 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq24984
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq24984
    | exact resolve eq24984 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24984
  have eq24999 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq814 x y
       have i₂ := eq24986
       grind)
    | exact superpose eq24986 eq814
    | (have j0 := eq814 x y
       grind)
    | (have r₁ := eq814 x y
       have r₂ := eq24986
       grind)
    | exact resolve eq814 eq24986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24986
  have eq25020 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq24999
  have eq25021 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq25020
  have eq25025 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq814 x y
       grind)
    | (have r₁ := eq25021
       have r₂ := eq814 x y
       grind)
    | exact resolve eq25021 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq25021
  have eq25028 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25025
       grind)
    | exact superpose eq25025 eq16
    | exact resolve eq16 eq25025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25038 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq25025
       grind)
    | exact superpose eq25025 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq25025
       grind)
    | exact resolve eq12 eq25025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25025
  have eq25039 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq25038
  have eq25041 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq25039
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq25039
    | exact resolve eq25039 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25039
  have eq25052 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25041
       grind)
    | exact superpose eq25041 eq10
    | exact resolve eq10 eq25041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25041
  have eq25152 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq25052
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25052
    | exact resolve eq25052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25052
  have eq25187 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25152
       grind)
    | exact superpose eq25152 eq16
    | exact resolve eq16 eq25152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25152
  have eq25188 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq25187
       have r₂ := eq13069 x
       grind)
    | exact resolve eq25187 eq13069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25187
  have eq25198 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq25188
       grind)
    | exact superpose eq25188 eq10
    | exact resolve eq10 eq25188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25188
  have eq25299 : x = (k x y) := by
    first
    | (have i₁ := eq25198
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25198
    | exact resolve eq25198 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25198
  have eq25348 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4879 x y
       have i₂ := eq25299
       grind)
    | exact superpose eq25299 eq4879
    | (have j0 := eq4879 x y
       grind)
    | (have r₁ := eq4879 x y
       have r₂ := eq25299
       grind)
    | exact resolve eq4879 eq25299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4879 eq25299
  have eq25362 : x = (M.op x y) ∨ x = y := by grind
  clear eq25348
  have eq25366 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25028
       have i₂ := eq25362
       grind)
    | exact superpose eq25362 eq25028
    | exact resolve eq25028 eq25362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25028 eq25362
  have eq25373 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq25366
  have eq25374 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25373
       grind)
    | exact superpose eq25373 eq16
    | exact resolve eq16 eq25373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25373
  have eq25379 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq25374
       have r₂ := eq13069 x
       grind)
    | exact resolve eq25374 eq13069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13069 eq25374
  have eq25380 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25379
       grind)
    | exact superpose eq25379 eq16
    | exact resolve eq16 eq25379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25381 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25379
       grind)
    | exact superpose eq25379 eq10
    | exact resolve eq10 eq25379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25379
  have eq25481 : x = y := by
    first
    | (have i₁ := eq25381
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25381
    | exact resolve eq25381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25381
  have eq25482 : (σ (M.op x y)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq25380
       have i₂ := eq722 x
       grind)
    | exact superpose eq722 eq25380
    | exact resolve eq25380 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq25380
  have eq25496 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq25482
       have i₂ := eq727 x
       grind)
    | exact superpose eq727 eq25482
    | exact resolve eq25482 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq25482
  have eq25509 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq25496
       have i₂ := eq25481
       grind)
    | exact superpose eq25481 eq25496
    | exact resolve eq25496 eq25481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25481 eq25496
  have eq25510 : False := by grind
  exact eq25510

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq14 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 x
       have i₂ := eq14 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq61 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq10
    | exact resolve eq10 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq43
    | exact resolve eq43 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq68 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq49
    | exact resolve eq49 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq68
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq68
    | exact resolve eq68 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq70 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq66
    | exact resolve eq66 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq75
    | (have j0 := eq75 (σ X0) (σ X1)
       grind)
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq44
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq44 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85
    | exact resolve eq85 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq95 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq100 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq75 sF3 (σ X0)
       grind)
    | exact superpose eq75 eq36
    | (have j1 := eq75 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq104 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq64 sF3
       grind)
    | exact superpose eq64 eq100
    | exact resolve eq100 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq64 y
       grind)
    | exact superpose eq64 eq104
    | exact resolve eq104 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq113 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq16
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq101 eq16
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq120 : (M.op x y) ≠ (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq121 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  have eq141 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq37
  have eq155 : ∀ X0 : G, (σ (k (k (M.op x y) x) X0)) = (k (k (σ (M.op x y)) (σ x)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq141 eq10
    | exact resolve eq10 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq141 eq16
    | exact resolve eq16 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq250 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq64 (τ X0)
       grind)
    | exact superpose eq64 eq34
    | exact resolve eq34 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq75 (τ X0) X1
       grind)
    | exact superpose eq75 eq34
    | (have j1 := eq75 (τ X0) X1
       grind)
    | exact resolve eq34 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (τ X0) X1) X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq261 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq250 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq250
    | exact resolve eq250 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq263 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq261 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq261
    | exact resolve eq261 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq261
  have eq282 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq371 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 (τ X1)) X2
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (k X1 (τ X0))
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq71
    | exact resolve eq71 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq71
    | exact resolve eq71 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : (σ (M.op (k (M.op x y) x) (k (M.op x y) x))) = (M.op (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq141 eq71
    | exact resolve eq71 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq51
    | exact resolve eq51 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq14
    | exact resolve eq14 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq254 X2 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq254
    | exact resolve eq254 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq75 X0 (σ X1)
       grind)
    | exact superpose eq75 eq254
    | (have j1 := eq75 X0 (σ X1)
       grind)
    | exact resolve eq254 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq536 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (σ X0) X1 X2
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq50
    | exact resolve eq50 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X0 X0))) (M.op X2 (M.op X3 (M.op X0 X0))))) = (M.op (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X0 X0))) (M.op X2 (M.op X3 (M.op X0 X0))))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X2 (M.op X3 (M.op X0 X0))) X1 X0
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq50 X1 X0 X3
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq50 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y X0 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq263 X0
       grind)
    | exact superpose eq263 eq16
    | exact resolve eq16 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq662 : ∀ X0 : G, (k (k (M.op x y) x) (τ X0)) = (τ (k (k (σ (M.op x y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq141 eq373
    | exact resolve eq373 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq75 (σ X0) X1
       grind)
    | exact superpose eq75 eq373
    | (have j1 := eq75 (σ X0) X1
       grind)
    | exact resolve eq373 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq695 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq93 eq75
    | (have j0 := eq75 (σ x) (σ y)
       grind)
    | exact resolve eq75 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq706
    | exact resolve eq706 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq710 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq707
       have r₂ := eq27
       grind)
    | exact resolve eq707 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq712 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq710
    | exact resolve eq710 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq714 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq712 eq121
    | (have r₁ := eq121
       have r₂ := eq712
       grind)
    | exact resolve eq121 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq715 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq712 eq62
    | (have r₁ := eq62
       have r₂ := eq712
       grind)
    | exact resolve eq62 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq712
  have eq725 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq715
  have eq726 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq714
  have eq728 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq750 : ∀ X0 X1 X2 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq728 (k X1 (τ X0)) X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq728
    | exact resolve eq728 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq751 : ∀ X0 X1 X2 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq728 (k (τ X0) X1) X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq728
    | exact resolve eq728 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq728 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq833 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq725 eq113
    | exact resolve eq113 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq725
  have eq904 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq726 eq128
    | exact resolve eq128 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq1681 : (k y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq904 eq833
    | exact resolve eq833 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq904
  have eq1703 : (k y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1681
  have eq3510 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq102 eq13
    | (have j0 := eq13 (σ X0) (σ y)
       have j1 := eq102 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ y)
       have r₂ := eq102 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq102 y
       grind)
    | exact resolve eq13 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq3512 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3510 X0
       have j1 := eq13 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3510 X0
       have r₂ := eq13 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3510 y
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3510 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3510
  have eq3524 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq3512
    | (have j0 := eq3512 X0
       grind)
    | exact resolve eq3512 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3512
  have eq5036 : ∀ X0 : G, (k (σ y) X0) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq794 y (τ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq794
    | (have j0 := eq794 y (τ X0)
       grind)
    | exact resolve eq794 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq794
  have eq5071 : ∀ X0 : G, (k (σ y) X0) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5036 X0
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq5036
    | (have j0 := eq5036 X0
       grind)
    | exact resolve eq5036 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5036
  have eq5109 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ y) X0) ∨ (k (σ y) X0) ≠ (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5071 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5071
    | (have j0 := eq5071 X0
       grind)
    | exact resolve eq5071 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5071
  have eq5144 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ y) X0) ∨ (k (σ y) X0) ≠ (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5109 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5109
    | (have j0 := eq5109 X0
       grind)
    | exact resolve eq5109 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5109
  have eq5170 : ∀ X0 : G, (k (σ y) X0) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq5144 X0
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq5144
    | (have j0 := eq5144 X0
       grind)
    | exact resolve eq5144 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5144
  have eq5471 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq251 X0 (M.op X1 (M.op X2 (M.op (τ X0) (τ X0))))
       have i₂ := eq14 (τ X0) X1 X2
       grind)
    | exact superpose eq14 eq251
    | exact resolve eq251 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq5512 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5471 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5471
    | (have j0 := eq5471 X0 X1 X2
       grind)
    | exact resolve eq5471 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5471
  have eq5648 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq542 x X2 X0 X1
       grind)
    | exact superpose eq542 eq14
    | exact resolve eq14 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq6798 : ∀ X0 X1 X2 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) ≠ (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (M.op (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (σ X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (k (σ X0) X1) (σ X2)
       have i₂ := eq750 X0 X1 X2
       grind)
    | exact superpose eq750 eq12
    | (have j0 := eq12 (k (σ X0) X1) (σ X2)
       have j1 := eq750 X0 X1 X2
       grind)
    | exact resolve eq12 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6800 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) ≠ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq750 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq6802 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k (σ X0) X1)) = (σ (M.op X2 X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) ≠ (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6798 X0 X1 X2
       have i₂ := eq71 X2
       grind)
    | exact superpose eq71 eq6798
    | (have j0 := eq6798 X0 X1 X2
       grind)
    | exact resolve eq6798 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6798
  have eq6842 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (M.op (σ X2) (k (σ X0) X1)) = (σ (M.op X2 X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) ≠ (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6802 X0 X1 X2
       have i₂ := eq371 X0 X1 X2
       grind)
    | exact superpose eq371 eq6802
    | (have j0 := eq6802 X0 X1 X2
       grind)
    | exact resolve eq6802 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq6802
  have eq7175 : ∀ X0 X1 X2 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) ≠ (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (M.op (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (σ X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (k X0 (σ X1)) (σ X2)
       have i₂ := eq751 X0 X1 X2
       grind)
    | exact superpose eq751 eq12
    | (have j0 := eq12 (k X0 (σ X1)) (σ X2)
       have j1 := eq751 X0 X1 X2
       grind)
    | exact resolve eq12 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7177 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) ≠ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq751 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq7179 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) ≠ (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7175 X0 X1 X2
       have i₂ := eq71 X2
       grind)
    | exact superpose eq71 eq7175
    | (have j0 := eq7175 X0 X1 X2
       grind)
    | exact resolve eq7175 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7175
  have eq7223 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) ≠ (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7179 X0 X1 X2
       have i₂ := eq252 X0 X1 X2
       grind)
    | exact superpose eq252 eq7179
    | (have j0 := eq7179 X0 X1 X2
       grind)
    | exact resolve eq7179 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq7179
  have eq56740 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3524 x
       have i₂ := eq1703
       grind)
    | exact superpose eq1703 eq3524
    | (have j0 := eq3524 x
       grind)
    | exact resolve eq3524 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq56800 : (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq56740
       have r₂ := eq106
       grind)
    | exact resolve eq56740 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56740
  have eq56830 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq56800
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56800
    | exact resolve eq56800 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56800
  have eq56845 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq56830
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq56830
    | exact resolve eq56830 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56830
  have eq56854 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq56845
    | exact resolve eq56845 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56845
  have eq56855 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq56854
  have eq56866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq56855 eq93
    | exact resolve eq93 eq56855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq56855
  have eq56888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq56866
  have eq56892 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq56888
       have r₂ := eq27
       grind)
    | exact resolve eq56888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56888
  have eq56896 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq61
       have i₂ := eq56892
       grind)
    | exact superpose eq56892 eq61
    | (have r₁ := eq61
       have r₂ := eq56892
       grind)
    | exact resolve eq61 eq56892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq56897 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq56892
       grind)
    | exact superpose eq56892 eq70
    | exact resolve eq70 eq56892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56899 : (M.op x y) ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq56892
       grind)
    | exact superpose eq56892 eq120
    | (have r₁ := eq120
       have r₂ := eq56892
       grind)
    | exact resolve eq120 eq56892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq56910 : ∀ X0 X1 : G, x = (M.op x (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1
       have i₂ := eq56892
       grind)
    | exact superpose eq56892 eq14
    | exact resolve eq14 eq56892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56915 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq478 x
       have i₂ := eq56892
       grind)
    | exact superpose eq56892 eq478
    | exact resolve eq478 eq56892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56916 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq481 x X0 X1
       have i₂ := eq56892
       grind)
    | exact superpose eq56892 eq481
    | exact resolve eq481 eq56892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq56927 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq56899
  have eq56928 : (k y x) = (M.op y x) := by grind
  clear eq56896
  have eq56931 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq20 eq56916
    | (have j0 := eq56916 X0 X1
       grind)
    | exact resolve eq56916 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56916
  have eq56932 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq56915
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56915
    | exact resolve eq56915 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56915
  have eq56942 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq56897
    | exact resolve eq56897 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56897
  have eq56944 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq56931 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56931
    | (have j0 := eq56931 X0 X1
       grind)
    | exact resolve eq56931 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56931
  have eq56945 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq56932
    | exact resolve eq56932 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56932
  have eq57222 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq56942 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq56942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57228 : (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ x))) := by
    first
    | exact superpose eq56942 eq478
    | exact resolve eq478 eq56942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq57237 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq56942 eq50
    | exact resolve eq50 eq56942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq57259 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq56928
       grind)
    | exact superpose eq56928 eq99
    | exact resolve eq99 eq56928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq57351 : (M.op (σ y) (σ y)) ≠ (σ (M.op y x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3524 x
       have i₂ := eq56928
       grind)
    | exact superpose eq56928 eq3524
    | (have j0 := eq3524 x
       grind)
    | exact resolve eq3524 eq56928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524 eq56928
  have eq57358 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq57351
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq57351
    | exact resolve eq57351 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57351
  have eq57361 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq57358
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq57358
    | exact resolve eq57358 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57358
  have eq57364 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) ≠ (σ (M.op y x)) := by
    first
    | exact superpose eq26 eq57361
    | exact resolve eq57361 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57361
  have eq57479 : ∀ X0 X1 : G, x = (M.op x (M.op X1 (M.op X0 (M.op y y)))) := by
    intro X0 X1
    first
    | exact superpose eq544 eq56910
    | exact resolve eq56910 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq56910
  have eq57945 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ (M.op x y)))) = (M.op (M.op X0 (M.op X1 (σ (M.op x y)))) (M.op X2 (M.op (σ x) (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq56944 eq5648
    | exact resolve eq5648 eq56944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57953 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ (M.op x y)))) = (M.op (M.op X0 (M.op X1 (σ (M.op x y)))) (M.op X2 (σ (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq56942 eq57945
    | exact resolve eq57945 eq56942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57945
  have eq58208 : (τ (σ (σ (M.op x y)))) = (k (τ (σ (σ (M.op x y)))) (σ x)) ∨ (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq57228 eq514
    | exact resolve eq514 eq57228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514 eq57228
  have eq58299 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | (have i₁ := eq58208
       have i₂ := eq16 sF1
       grind)
    | exact superpose eq16 eq58208
    | exact resolve eq58208 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58208
  have eq58349 : (σ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq58299
       have i₂ := eq71 sF1
       grind)
    | exact superpose eq71 eq58299
    | exact resolve eq58299 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq58299
  have eq58416 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq536 x X1 x
       have i₂ := eq56892
       grind)
    | exact superpose eq56892 eq536
    | exact resolve eq536 eq56892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq58783 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq58416 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq58416
    | (have j0 := eq58416 X0 X1
       grind)
    | exact resolve eq58416 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58416
  have eq58799 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq20 eq58783
    | (have j0 := eq58783 X0 X1
       grind)
    | exact resolve eq58783 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58783
  have eq59738 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op (M.op X0 (M.op x x)) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq540 (M.op y y) x x x
       have i₂ := eq57479 (M.op y y) x
       grind)
    | exact superpose eq57479 eq540
    | exact resolve eq540 eq57479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq57479
  have eq59759 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq59738 X0
       have i₂ := eq56892
       grind)
    | exact superpose eq56892 eq59738
    | exact resolve eq59738 eq56892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59738
  have eq60490 : ∀ X0 X1 : G, y = (M.op y (M.op X1 (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq59759 eq14
    | exact resolve eq14 eq59759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59759
  have eq60504 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq60490 eq14
    | exact resolve eq14 eq60490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60490
  have eq62045 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq56927
       grind)
    | exact superpose eq56927 eq106
    | exact resolve eq106 eq56927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq56927
  have eq62090 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq62045
       have i₂ := eq57259
       grind)
    | exact superpose eq57259 eq62045
    | exact resolve eq62045 eq57259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62045
  have eq63893 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq62090 eq75
    | (have j0 := eq75 x y
       grind)
    | exact resolve eq75 eq62090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63894 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq63893
  have eq65374 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (τ (σ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq58349 eq16
    | exact resolve eq16 eq58349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58349
  have eq65495 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq65374
       have i₂ := eq16 sF1
       grind)
    | exact superpose eq16 eq65374
    | exact resolve eq65374 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65374
  have eq65506 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq65495 eq156
    | exact resolve eq156 eq65495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65495
  have eq65517 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq65506
    | exact resolve eq65506 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65506
  have eq65877 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq65517 eq56944
    | exact resolve eq56944 eq65517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67951 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (M.op (σ y) (σ x))))) ∨ (M.op x y) = (k x y) := by
    intro X0 X1
    first
    | exact superpose eq63894 eq14
    | exact resolve eq14 eq63894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67953 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq63894 eq51
    | exact resolve eq51 eq63894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq63894
  have eq68368 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq65517 eq65877
    | exact resolve eq65877 eq65517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65517
  have eq68371 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq65877 eq56944
    | exact resolve eq56944 eq65877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65877
  have eq68383 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq68368
  have eq68390 : (M.op x y) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq56942 eq68371
    | exact resolve eq68371 eq56942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68371
  have eq68813 : (σ (M.op x y)) ≠ (σ x) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq68383 eq57222
    | (have j0 := eq57222 (σ (M.op x y))
       grind)
    | exact resolve eq57222 eq68383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57222 eq68383
  have eq68826 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | (have r₁ := eq68813
       have r₂ := eq68390
       grind)
    | exact resolve eq68813 eq68390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68390 eq68813
  have eq68827 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq56945 eq68826
    | exact resolve eq68826 eq56945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56945 eq68826
  have eq69184 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq68827 eq156
    | exact resolve eq156 eq68827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq68827
  have eq69197 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq69184
    | exact resolve eq69184 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69184
  have eq69198 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq69197
  have eq69204 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq69198 eq141
    | exact resolve eq141 eq69198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69236 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq69204
    | exact resolve eq69204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69204
  have eq72716 : (k (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq57364
       have i₂ := eq57259
       grind)
    | exact superpose eq57259 eq57364
    | exact resolve eq57364 eq57259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57259 eq57364
  have eq73088 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq62090 eq72716
    | (have r₁ := eq72716
       have r₂ := eq62090
       grind)
    | exact resolve eq72716 eq62090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62090 eq72716
  have eq73094 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq73088
  have eq73099 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq73094 eq55
    | exact resolve eq55 eq73094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73094
  have eq73144 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x y) := by grind
  clear eq73099
  have eq81242 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X2 (M.op X0 (M.op X1 (σ (M.op x y)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq57953 eq14
    | exact resolve eq14 eq57953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57953
  have eq109382 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X1 (M.op X0 (σ (M.op x y))))) ∨ (M.op x y) = (k x y) := by
    intro X0 X1
    first
    | exact superpose eq58799 eq67951
    | exact resolve eq67951 eq58799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67951
  have eq109418 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq109382 eq81242
    | exact resolve eq81242 eq109382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81242
  have eq120040 : ∀ X0 : G, (k (k (M.op x y) x) (τ X0)) = (τ (M.op (k (σ (M.op x y)) (σ x)) X0)) ∨ (σ (M.op (k (M.op x y) x) (k (M.op x y) x))) = (M.op (k (σ (M.op x y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq141 eq695
    | exact resolve eq695 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120045 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ (σ (M.op x x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq695 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq695
    | (have j0 := eq695 x X0
       grind)
    | exact resolve eq695 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq120273 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) ∨ (σ (M.op x x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq120045 X0
       have i₂ := eq282 X0
       grind)
    | exact superpose eq282 eq120045
    | (have j0 := eq120045 X0
       grind)
    | exact resolve eq120045 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq120045
  have eq120275 : ∀ X0 : G, (k (k (M.op x y) x) (τ X0)) = (τ (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op (k (M.op x y) x) (k (M.op x y) x))) = (M.op (k (σ (M.op x y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq69236 eq120040
    | (have j0 := eq120040 X0
       grind)
    | exact resolve eq120040 eq69236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120040
  have eq120337 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq120273 X0
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq120273
    | (have j0 := eq120273 X0
       grind)
    | exact resolve eq120273 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq120273
  have eq120339 : ∀ X0 : G, (τ (k (k (σ (M.op x y)) (σ x)) X0)) = (τ (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op (k (M.op x y) x) (k (M.op x y) x))) = (M.op (k (σ (M.op x y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq662 eq120275
    | (have j0 := eq120275 X0
       grind)
    | exact resolve eq120275 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120275
  have eq120381 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq56942 eq120337
    | (have j0 := eq120337 X0
       grind)
    | exact resolve eq120337 eq56942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120337
  have eq120382 : ∀ X0 : G, (τ (k (σ (M.op x y)) X0)) = (τ (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op (k (M.op x y) x) (k (M.op x y) x))) = (M.op (k (σ (M.op x y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq69236 eq120339
    | (have j0 := eq120339 X0
       grind)
    | exact resolve eq120339 eq69236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120339
  have eq120407 : ∀ X0 : G, (σ (M.op (k (M.op x y) x) (k (M.op x y) x))) = (M.op (σ (M.op x y)) X0) ∨ (τ (k (σ (M.op x y)) X0)) = (τ (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq69236 eq120382
    | (have j0 := eq120382 X0
       grind)
    | exact resolve eq120382 eq69236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120382
  have eq120432 : ∀ X0 : G, (M.op (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) = (M.op (σ (M.op x y)) X0) ∨ (τ (k (σ (M.op x y)) X0)) = (τ (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq472 eq120407
    | (have j0 := eq120407 X0
       grind)
    | exact resolve eq120407 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq120407
  have eq120453 : ∀ X0 : G, (τ (k (σ (M.op x y)) X0)) = (τ (M.op (σ (M.op x y)) X0)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq69236 eq120432
    | (have j0 := eq120432 X0
       grind)
    | exact resolve eq120432 eq69236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120432
  have eq120586 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120381 eq55
    | (have j1 := eq120381 (σ y)
       grind)
    | exact resolve eq55 eq120381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq120381
  have eq120921 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq120586
    | exact resolve eq120586 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120586
  have eq120931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq120921
    | exact resolve eq120921 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq120921
  have eq120934 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq120931
       have r₂ := eq27
       grind)
    | exact resolve eq120931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120931
  have eq120937 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq44
       have i₂ := eq120934
       grind)
    | exact superpose eq120934 eq44
    | exact resolve eq44 eq120934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120999 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq120937
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq120937
    | exact resolve eq120937 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120937
  have eq130152 : (k (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq163 eq120453
    | (have j0 := eq120453 (σ y)
       grind)
    | exact resolve eq120453 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq120453
  have eq131349 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq109418 eq130152
    | exact resolve eq130152 eq109418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109418 eq130152
  have eq131545 : (M.op x y) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq30 eq131349
    | exact resolve eq131349 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq131349
  have eq131556 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq131545
       have i₂ := eq120934
       grind)
    | exact superpose eq120934 eq131545
    | exact resolve eq131545 eq120934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131545
  have eq131575 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq131556 eq56944
    | exact resolve eq56944 eq131556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56944
  have eq131579 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ x))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq131556 eq58799
    | exact resolve eq58799 eq131556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58799
  have eq131582 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq131556 eq109382
    | exact resolve eq109382 eq131556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131613 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k (M.op x y) y) := by
    intro X0
    first
    | (have j0 := eq131582 X0
       grind)
    | (have r₁ := eq131582 X0
       have r₂ := eq73144
       grind)
    | exact resolve eq131582 eq73144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131582
  have eq131621 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq131613 X0
       have i₂ := eq120934
       grind)
    | exact superpose eq120934 eq131613
    | (have j0 := eq131613 X0
       grind)
    | exact resolve eq131613 eq120934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131613
  have eq149094 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq131556 eq131575
    | exact resolve eq131575 eq131556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149099 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq131575 eq109382
    | exact resolve eq109382 eq131575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109382 eq131575
  have eq149114 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq149094
  have eq149122 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have r₁ := eq149099
       have r₂ := eq73144
       grind)
    | exact resolve eq149099 eq73144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149099
  have eq149125 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq149122
       have i₂ := eq120934
       grind)
    | exact superpose eq120934 eq149122
    | exact resolve eq149122 eq120934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149122
  have eq150607 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ x)))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq149114 eq5648
    | exact resolve eq5648 eq149114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5648 eq149114
  have eq150613 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq56942 eq150607
    | exact resolve eq150607 eq56942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56942 eq150607
  have eq150737 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq149125 eq67953
    | exact resolve eq67953 eq149125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67953
  have eq150751 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have r₁ := eq150737
       have r₂ := eq73144
       grind)
    | exact resolve eq150737 eq73144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73144 eq150737
  have eq150754 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq150751
       have i₂ := eq120934
       grind)
    | exact superpose eq120934 eq150751
    | exact resolve eq150751 eq120934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150751
  have eq153174 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq149125 eq131579
    | exact resolve eq131579 eq149125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131579 eq149125
  have eq153194 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq153174
  have eq154033 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq153194 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq13 eq153194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153194
  have eq154034 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq154033
       have r₂ := eq131556
       grind)
    | exact resolve eq154033 eq131556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154033
  have eq154300 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq131556 eq131621
    | exact resolve eq131621 eq131556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131621
  have eq154320 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) y) := by grind
  clear eq154300
  have eq171198 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) = (k (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq150613 eq13
    | (have j0 := eq13 (M.op X0 (σ (M.op x y))) (σ (M.op x y))
       grind)
    | exact resolve eq13 eq150613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150613
  have eq171202 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) = (k (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq171198 X0
       grind)
    | (have r₁ := eq171198 X0
       have r₂ := eq131556
       grind)
    | exact resolve eq171198 eq131556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131556 eq171198
  have eq171207 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (k (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq57237 eq171202
    | exact resolve eq171202 eq57237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57237 eq171202
  have eq190772 : (k y (M.op x y)) = (τ (M.op (σ y) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq154034 eq119
    | exact resolve eq119 eq154034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq154034
  have eq230397 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5512 X0 X1 X2
       have i₂ := eq637 X0
       grind)
    | exact superpose eq637 eq5512
    | (have j0 := eq5512 X0 X1 X2
       grind)
    | exact resolve eq5512 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5512
  have eq230398 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (τ (M.op X0 X0)))))) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq230397 X0 X1 X2
       have i₂ := eq637 X0
       grind)
    | exact superpose eq637 eq230397
    | (have j0 := eq230397 X0 X1 X2
       grind)
    | exact resolve eq230397 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq230397
  have eq230676 : ∀ X0 X1 : G, (σ x) = (σ (k x (M.op X0 (M.op X1 (τ (M.op (σ x) (σ x))))))) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X1 (M.op x (τ (M.op sF2 sF2))))
       have i₂ := eq230398 sF2 X1 x
       grind)
    | exact superpose eq230398 eq35
    | (have j1 := eq230398 (σ x) X1 x
       grind)
    | exact resolve eq35 eq230398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq230398
  have eq231021 : ∀ X0 X1 : G, (σ x) = (σ (k x (M.op X0 (M.op X1 (M.op x x))))) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq69 eq230676
    | exact resolve eq230676 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230676
  have eq231239 : ∀ X0 X1 : G, (σ x) = (σ (k x (M.op X0 (M.op X1 (M.op x y))))) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq231021 X0 X1
       have i₂ := eq56892
       grind)
    | exact superpose eq56892 eq231021
    | exact resolve eq231021 eq56892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231021
  have eq231400 : ∀ X0 X1 : G, (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ (k x (M.op X0 (M.op X1 (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq69 eq231239
    | (have j0 := eq231239 X0 X1
       grind)
    | exact resolve eq231239 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq231239
  have eq231542 : ∀ X0 X1 : G, (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ (k x (M.op X0 (M.op X1 (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq231400 X0 X1
       have i₂ := eq56892
       grind)
    | exact superpose eq56892 eq231400
    | (have j0 := eq231400 X0 X1
       grind)
    | exact resolve eq231400 eq56892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56892 eq231400
  have eq231610 : ∀ X0 X1 : G, (σ x) = (σ (k x (M.op X0 (M.op X1 (M.op x y))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28 eq231542
    | (have j0 := eq231542 X0 X1
       grind)
    | exact resolve eq231542 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231542
  have eq231764 : ∀ X0 X1 : G, (τ (σ x)) = (k x (M.op X0 (M.op X1 (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq231610 eq16
    | exact resolve eq16 eq231610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231610
  have eq231928 : ∀ X0 X1 : G, x = (k x (M.op X0 (M.op X1 (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28 eq231764
    | exact resolve eq231764 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq231764
  have eq599146 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) ≠ (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6800 X0 X1 X2
       have i₂ := eq463 X0 X1
       grind)
    | exact superpose eq463 eq6800
    | (have j0 := eq6800 X0 X1 X2
       grind)
    | exact resolve eq6800 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6800
  have eq605470 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) ≠ (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7177 X0 X1 X2
       have i₂ := eq464 X0 X1
       grind)
    | exact superpose eq464 eq7177
    | (have j0 := eq7177 X0 X1 X2
       grind)
    | exact resolve eq7177 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7177
  have eq823321 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq154320 eq171207
    | exact resolve eq171207 eq154320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154320 eq171207
  have eq823343 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq823321
  have eq823380 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq823343 eq5170
    | (have j0 := eq5170 (σ (M.op x y))
       grind)
    | exact resolve eq5170 eq823343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5170 eq823343
  have eq823397 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq823380
       have r₂ := eq150754
       grind)
    | exact resolve eq823380 eq150754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150754 eq823380
  have eq823946 : (M.op y y) = (τ (M.op (σ y) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq823397 eq128
    | exact resolve eq128 eq823397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq823397
  have eq825689 : (k y (M.op x y)) = (M.op y y) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq823946 eq190772
    | exact resolve eq190772 eq823946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190772 eq823946
  have eq826166 : (k y (M.op x y)) = (M.op y y) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq825689
  have eq826241 : (M.op y y) = (M.op y (M.op x y)) ∨ (M.op y y) = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq826166 eq75
    | (have j0 := eq75 y (M.op x y)
       grind)
    | exact resolve eq75 eq826166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq826166
  have eq826256 : (M.op y y) = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq826241
  have eq826422 : (M.op y y) ≠ (M.op y y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq826256 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq826256
       grind)
    | exact resolve eq13 eq826256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826256
  have eq826428 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq826422
  have eq826430 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60504 eq826428
    | exact resolve eq826428 eq60504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60504 eq826428
  have eq826431 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq826430
  have eq1302955 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k (σ X0) X1)) = (σ (M.op X2 X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) ≠ (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6842 X0 X1 X2
       have j1 := eq599146 X0 X1 X2
       grind)
    | (have r₁ := eq6842 X0 X1 X2
       have r₂ := eq599146 X0 X1 X2
       grind)
    | exact resolve eq6842 eq599146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6842 eq599146
  have eq1302956 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (σ X2) (k (σ X0) X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1302955 X0 X1 X2
       grind)
    | (have r₁ := eq1302955 X0 X1 X2
       have r₂ := eq463 X0 X1
       grind)
    | exact resolve eq1302955 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq1302955
  have eq1304919 : ∀ X0 X1 : G, (σ (k (k (k (M.op x y) x) (τ X0)) X1)) = (M.op (k (k (σ (M.op x y)) (σ x)) X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (k (k (σ (M.op x y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq141 eq1302956
    | exact resolve eq1302956 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1302956
  have eq1306187 : ∀ X0 X1 : G, (M.op (k (σ (M.op x y)) X0) (σ X1)) = (σ (k (k (k (M.op x y) x) (τ X0)) X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (k (k (σ (M.op x y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq69236 eq1304919
    | (have j0 := eq1304919 X0 X1
       grind)
    | exact resolve eq1304919 eq69236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304919
  have eq1306414 : ∀ X0 X1 : G, (M.op (k (σ (M.op x y)) X0) (σ X1)) = (σ (k (τ (k (k (σ (M.op x y)) (σ x)) X0)) X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (k (k (σ (M.op x y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq662 eq1306187
    | (have j0 := eq1306187 X0 X1
       grind)
    | exact resolve eq1306187 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq1306187
  have eq1306620 : ∀ X0 X1 : G, (M.op (k (σ (M.op x y)) X0) (σ X1)) = (k (k (k (σ (M.op x y)) (σ x)) X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (k (k (σ (M.op x y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1306414 X0 X1
       have i₂ := eq34 (k (k sF1 sF2) X0) X1
       grind)
    | exact superpose eq34 eq1306414
    | (have j0 := eq1306414 X0 X1
       grind)
    | exact resolve eq1306414 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306414
  have eq1306781 : ∀ X0 X1 : G, (k (k (σ (M.op x y)) X0) (σ X1)) = (M.op (k (σ (M.op x y)) X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (k (k (σ (M.op x y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq69236 eq1306620
    | (have j0 := eq1306620 X0 X1
       grind)
    | exact resolve eq1306620 eq69236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306620
  have eq1306879 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (k (σ (M.op x y)) X0)) ∨ (k (k (σ (M.op x y)) X0) (σ X1)) = (M.op (k (σ (M.op x y)) X0) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq69236 eq1306781
    | (have j0 := eq1306781 X0 X1
       grind)
    | exact resolve eq1306781 eq69236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306781
  have eq1306959 : ∀ X0 X1 : G, (k (k (σ (M.op x y)) X0) (σ X1)) = (M.op (k (σ (M.op x y)) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1306879 X0 X1
       have j1 := eq480 X1 (k (σ (M.op x y)) X0)
       grind)
    | (have r₁ := eq1306879 X0 X0
       have r₂ := eq480 X0 (k (σ (M.op x y)) X0)
       grind)
    | exact resolve eq1306879 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306879
  have eq1308015 : ∀ X0 : G, (σ (k (k (M.op x y) x) X0)) = (M.op (k (σ (M.op x y)) (σ x)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1306959 eq155
    | exact resolve eq155 eq1306959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq1306959
  have eq1308274 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ X0)) = (σ (k (k (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq69236 eq1308015
    | exact resolve eq1308015 eq69236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69236 eq1308015
  have eq1308378 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq69198 eq1308274
    | exact resolve eq1308274 eq69198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69198 eq1308274
  have eq1308525 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq1308378 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1308378
    | exact resolve eq1308378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308378
  have eq1309440 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq135 eq1308525
    | exact resolve eq1308525 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308525
  have eq1319155 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) ≠ (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq7223 X0 X1 X2
       have j1 := eq605470 X0 X1 X2
       grind)
    | (have r₁ := eq7223 X0 X1 X2
       have r₂ := eq605470 X0 X1 X2
       grind)
    | exact resolve eq7223 eq605470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7223 eq605470
  have eq1319156 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1319155 X0 X1 X2
       grind)
    | (have r₁ := eq1319155 X0 X1 X2
       have r₂ := eq464 X0 X1
       grind)
    | exact resolve eq1319155 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq1319155
  have eq1319845 : ∀ X0 X1 X2 : G, (σ (k (k (τ X1) (k (M.op x y) (τ X0))) X2)) = (M.op (k X1 (k (σ (M.op x y)) X0)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X1 (k (σ (M.op x y)) X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq135 eq1319156
    | exact resolve eq1319156 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1319156
  have eq1321332 : ∀ X0 X1 X2 : G, (σ (k (k (τ X1) (k (M.op x y) (τ X0))) X2)) = (M.op (k X1 (M.op (σ (M.op x y)) X0)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X1 (k (σ (M.op x y)) X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1309440 eq1319845
    | (have j0 := eq1319845 X0 X1 X2
       grind)
    | exact resolve eq1319845 eq1309440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319845
  have eq1321810 : ∀ X0 X1 X2 : G, (σ (k (τ (k X1 (k (σ (M.op x y)) X0))) X2)) = (M.op (k X1 (M.op (σ (M.op x y)) X0)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X1 (k (σ (M.op x y)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1321332 X1 X2 X2
       have i₂ := eq494 sF0 X1 X2
       grind)
    | exact superpose eq494 eq1321332
    | (have j0 := eq1321332 X0 X1 X2
       grind)
    | exact resolve eq1321332 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq1321332
  have eq1322131 : ∀ X0 X1 X2 : G, (k (k X1 (k (σ (M.op x y)) X0)) (σ X2)) = (M.op (k X1 (M.op (σ (M.op x y)) X0)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X1 (k (σ (M.op x y)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1321810 X0 X1 X1
       have i₂ := eq34 (k X1 (k (σ sF0) X0)) X1
       grind)
    | exact superpose eq34 eq1321810
    | (have j0 := eq1321810 X0 X1 X2
       grind)
    | exact resolve eq1321810 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1321810
  have eq1322351 : ∀ X0 X1 X2 : G, (k (k X1 (k (σ (M.op x y)) X0)) (σ X2)) = (M.op (k X1 (M.op (σ (M.op x y)) X0)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X1 (k (σ (M.op x y)) X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq20 eq1322131
    | (have j0 := eq1322131 X0 X1 X2
       grind)
    | exact resolve eq1322131 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322131
  have eq1322467 : ∀ X0 X1 X2 : G, (M.op (k X1 (M.op (σ (M.op x y)) X0)) (σ X2)) = (k (k X1 (M.op (σ (M.op x y)) X0)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X1 (k (σ (M.op x y)) X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1309440 eq1322351
    | (have j0 := eq1322351 X0 X1 X2
       grind)
    | exact resolve eq1322351 eq1309440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322351
  have eq1322560 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op (σ X2) (k X1 (M.op (σ (M.op x y)) X0))) ∨ (M.op (k X1 (M.op (σ (M.op x y)) X0)) (σ X2)) = (k (k X1 (M.op (σ (M.op x y)) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1309440 eq1322467
    | (have j0 := eq1322467 X0 X1 X2
       grind)
    | exact resolve eq1322467 eq1309440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309440 eq1322467
  have eq1322631 : ∀ X0 X1 X2 : G, (M.op (k X1 (M.op (σ (M.op x y)) X0)) (σ X2)) = (k (k X1 (M.op (σ (M.op x y)) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1322560 X0 X1 X2
       have j1 := eq480 X2 (k X1 (M.op (σ (M.op x y)) X0))
       grind)
    | (have r₁ := eq1322560 X0 X1 X0
       have r₂ := eq480 X0 (k X1 (M.op (σ (M.op x y)) X0))
       grind)
    | exact resolve eq1322560 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq1322560
  have eq1583104 : ∀ X1 : G, (k x (σ X1)) = (M.op x (σ X1)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq231928 eq1322631
    | exact resolve eq1322631 eq231928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231928 eq1322631
  have eq1584671 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1583104 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1583104
    | exact resolve eq1583104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583104
  have eq1586872 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1584671 y
       grind)
    | exact superpose eq1584671 eq44
    | exact resolve eq44 eq1584671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1584671
  have eq1587125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120999 eq1586872
    | exact resolve eq1586872 eq120999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120999 eq1586872
  have eq1587659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1587125
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1587125
    | exact resolve eq1587125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1587125
  have eq1587934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1587659
    | exact resolve eq1587659 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587659
  have eq1588063 : x = (M.op x y) := by
    first
    | (have r₁ := eq1587934
       have r₂ := eq27
       grind)
    | exact resolve eq1587934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587934
  have eq1588115 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1588063 eq20
    | exact resolve eq20 eq1588063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1588593 : x = (k x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1588063 eq826431
    | exact resolve eq826431 eq1588063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826431 eq1588063
  have eq1588965 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1588593
       have i₂ := eq120934
       grind)
    | exact superpose eq120934 eq1588593
    | exact resolve eq1588593 eq120934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120934 eq1588593
  have eq1588966 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1588965
  have eq1589389 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1588115
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1588115
    | exact resolve eq1588115 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588115
  have eq1593796 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1588966 eq15
    | exact resolve eq15 eq1588966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588966
  have eq1594767 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1593796
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1593796
    | exact resolve eq1593796 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1593796
  have eq1595055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1589389 eq1594767
    | exact resolve eq1594767 eq1589389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589389 eq1594767
  have eq1595218 : False := by grind
  exact eq1595218

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq293 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
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
  have eq298 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq299 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq429 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq299 X1 X0
       grind)
    | exact superpose eq299 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq299 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq299 X0 X1
       grind)
    | exact resolve eq13 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq299 (σ x) (σ y)
       grind)
    | exact superpose eq299 eq16
    | (have j1 := eq299 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq429 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq440 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq433
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq433
    | exact resolve eq433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq443 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq437 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq437 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq437 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq469 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq443 X1 (τ X0)
       grind)
    | exact superpose eq443 eq17
    | (have j1 := eq443 X1 (τ X0)
       grind)
    | exact resolve eq17 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq475 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq443 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq469 X1 (τ X0)
       grind)
    | exact superpose eq469 eq18
    | (have j1 := eq469 X1 (τ X0)
       grind)
    | exact resolve eq18 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq469
  have eq921 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq916 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq916
    | (have j0 := eq916 X0 X1
       grind)
    | exact resolve eq916 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq937 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq921 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq921
    | (have j0 := eq921 X0 X1
       grind)
    | exact resolve eq921 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq940 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq937 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq937
    | (have j0 := eq937 X0 X1
       grind)
    | exact resolve eq937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq1000 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq940 X0 X1
       have i₂ := eq443 X0 X1
       grind)
    | exact superpose eq443 eq940
    | (have j0 := eq940 X1 X0
       have j1 := eq443 X1 X0
       grind)
    | exact resolve eq940 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq940
  have eq1065 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1000 X0 X1
       have j1 := eq475 X0 X1
       grind)
    | (have r₁ := eq1000 X0 X1
       have r₂ := eq475 X0 X1
       grind)
    | exact resolve eq1000 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq1000
  have eq1108 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1065 X1 (σ X0)
       grind)
    | exact superpose eq1065 eq22
    | (have j1 := eq1065 X1 (σ X0)
       grind)
    | exact resolve eq22 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1065
  have eq1145 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1108 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1108
    | (have j0 := eq1108 X0 X1
       grind)
    | exact resolve eq1108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1167 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1145 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1145
    | (have j0 := eq1145 X0 X1
       grind)
    | exact resolve eq1145 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1951 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1167 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1167
    | exact resolve eq1167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq2019 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1951 x y
       grind)
    | exact superpose eq1951 eq16
    | (have j1 := eq1951 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1951 x y
       grind)
    | exact resolve eq16 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq2051 : y = (k x y) := by grind
  clear eq2019
  have eq3095 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq440
       have i₂ := eq299 x y
       grind)
    | exact superpose eq299 eq440
    | (have j1 := eq299 x y
       grind)
    | exact resolve eq440 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3098 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq3095
  have eq3099 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq3098
       have i₂ := eq2051
       grind)
    | exact superpose eq2051 eq3098
    | exact resolve eq3098 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098
  have eq3100 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3099
       have i₂ := eq2051
       grind)
    | exact superpose eq2051 eq3099
    | exact resolve eq3099 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099
  have eq3101 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq440
       have i₂ := eq3100
       grind)
    | exact superpose eq3100 eq440
    | exact resolve eq440 eq3100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq3100
  have eq3113 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3101
  have eq3114 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3113
       have i₂ := eq2051
       grind)
    | exact superpose eq2051 eq3113
    | exact resolve eq3113 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113
  have eq3115 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3114
  have eq3118 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3115
       grind)
    | exact superpose eq3115 eq16
    | exact resolve eq16 eq3115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3115
  have eq3152 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq3118
       have i₂ := eq299 x y
       grind)
    | exact superpose eq299 eq3118
    | (have j1 := eq299 x y
       grind)
    | exact resolve eq3118 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq3155 : (M.op x y) = (k x y) := by grind
  clear eq3152
  have eq3157 : y = (M.op x y) := by
    first
    | (have i₁ := eq3155
       have i₂ := eq2051
       grind)
    | exact superpose eq2051 eq3155
    | exact resolve eq3155 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051 eq3155
  have eq3158 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq3118
       have i₂ := eq3157
       grind)
    | exact superpose eq3157 eq3118
    | exact resolve eq3118 eq3157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118 eq3157
  have eq3172 : False := by grind
  exact eq3172
