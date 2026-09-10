import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq76 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq151 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq149 (τ X0)
       grind)
    | exact superpose eq149 eq18
    | exact resolve eq18 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq206 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X0 X0)))) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X2 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq53
    | exact resolve eq53 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq293 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (k X0 X1)) (M.op X2 (σ X1)))) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq9
    | (have j1 := eq83 X0 X1
       grind)
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq83 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq314 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq319 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq314 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq314 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq314 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq397 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq151 (τ X0)
       grind)
    | exact superpose eq151 eq18
    | exact resolve eq18 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq151
  have eq439 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq319 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq319
    | (have j0 := eq319 (τ X0) X1
       grind)
    | exact resolve eq319 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq449 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq439
    | (have j0 := eq439 X0 X1
       grind)
    | exact resolve eq439 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq456 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq449
    | (have j0 := eq449 X0 X1
       grind)
    | exact resolve eq449 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq846 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 X0 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq206
    | exact resolve eq206 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq5445 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq293
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq293
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq293 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq5448 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq5445
  have eq5450 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 (σ (τ X1))))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq294 (τ X0) (τ X1) X2
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq294
    | (have j0 := eq294 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq294 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq5563 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 X1))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5450 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5450
    | (have j0 := eq5450 X0 X1 X2
       grind)
    | exact resolve eq5450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5450
  have eq5567 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X1))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5563 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5563
    | (have j0 := eq5563 X0 X1 X2
       grind)
    | exact resolve eq5563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5563
  have eq5571 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X1))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5567 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5567
    | (have j0 := eq5567 X0 X1 X2
       grind)
    | exact resolve eq5567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5567
  have eq5572 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X1))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5571 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5571
    | (have j0 := eq5571 (σ (τ X1)) X1 X2
       grind)
    | exact resolve eq5571 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5571
  have eq5573 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X1))) = X2 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5572 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5572
    | (have j0 := eq5572 X0 X1 X2
       grind)
    | exact resolve eq5572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5572
  have eq8305 : ∀ X0 : G, (σ (k (σ (τ (τ X0))) (τ X0))) = (k X0 (σ (k (σ (τ (τ X0))) (τ X0)))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq397 X0
       have i₂ := eq89 (τ (τ X0)) (τ X0)
       grind)
    | exact superpose eq89 eq397
    | (have j1 := eq89 (τ (τ X0)) (τ X0)
       grind)
    | exact resolve eq397 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq8351 : ∀ X0 : G, (σ (k (σ (τ (τ X0))) (τ X0))) = (k X0 (σ (k (σ (τ (τ X0))) (τ X0)))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq8305 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8305
  have eq8386 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = (k X0 (k (σ (σ (τ (τ X0)))) X0)) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8351 X0
       have i₂ := eq19 X0 (σ (τ (τ X0)))
       grind)
    | exact superpose eq19 eq8351
    | (have j0 := eq8351 X0
       grind)
    | exact resolve eq8351 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8351
  have eq8414 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8386 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq8386
    | (have j0 := eq8386 X0
       grind)
    | exact resolve eq8386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8386
  have eq8422 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8414 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8414
    | (have j0 := eq8414 X0
       grind)
    | exact resolve eq8414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8414
  have eq9965 : ∀ X0 : G, (σ (σ (τ (τ X0)))) = (k X0 (σ (σ (τ (τ X0))))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq397 X0
       have i₂ := eq8422 X0
       grind)
    | exact superpose eq8422 eq397
    | (have j1 := eq8422 X0
       grind)
    | exact resolve eq397 eq8422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq8422
  have eq10079 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9965 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq9965
    | (have j0 := eq9965 X0
       grind)
    | exact resolve eq9965 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9965
  have eq10087 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10079 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10079
    | (have j0 := eq10079 X0
       grind)
    | exact resolve eq10079 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10079
  have eq25104 : ∀ X0 X1 : G, (k X1 X0) = (M.op (k X1 X0) X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (k X1 X0)
       have i₂ := eq5573 X1 X0 X0
       grind)
    | exact superpose eq5573 eq76
    | (have j1 := eq5573 X1 X0 x
       grind)
    | exact resolve eq76 eq5573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5573
  have eq25363 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25104 (k X0 X0) X0
       have i₂ := eq10087 X0
       grind)
    | exact superpose eq10087 eq25104
    | (have j0 := eq25104 (k X0 X0) (k X0 X0)
       have j1 := eq10087 X0
       grind)
    | exact resolve eq25104 eq10087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25104
  have eq25651 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25363
  have eq25673 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25651 X0
       have j1 := eq456 X0 X0
       grind)
    | (have r₁ := eq25651 X0
       have r₂ := eq456 X0 x
       grind)
    | exact resolve eq25651 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25651
  have eq25702 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X1 X1) = (k X1 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (k X0 X0)
       have i₂ := eq25673 X0
       grind)
    | exact superpose eq25673 eq12
    | (have j0 := eq12 X1 (k X0 X0)
       have j1 := eq25673 X0
       grind)
    | (have r₁ := eq12 X0 (k X0 X0)
       have r₂ := eq25673 X0
       grind)
    | exact resolve eq12 eq25673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25673
  have eq25802 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq25702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25702
  have eq26230 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10087 X0
       have i₂ := eq25802 X0 X0
       grind)
    | exact superpose eq25802 eq10087
    | (have j0 := eq10087 X0
       have j1 := eq25802 X0 x
       grind)
    | exact resolve eq10087 eq25802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10087 eq25802
  have eq26416 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26230 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26230
  have eq26480 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq26416 X0
       have j1 := eq456 X0 X0
       grind)
    | (have r₁ := eq26416 X0
       have r₂ := eq456 X0 x
       grind)
    | exact resolve eq26416 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq26416
  have eq26855 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq26480 (σ X0)
       grind)
    | exact superpose eq26480 eq15
    | exact resolve eq15 eq26480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26863 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq26480 (τ X0)
       grind)
    | exact superpose eq26480 eq32
    | exact resolve eq32 eq26480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq26910 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq26863 X0
       have i₂ := eq26480 X0
       grind)
    | exact superpose eq26480 eq26863
    | exact resolve eq26863 eq26480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26863
  have eq26918 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq26855 X0
       have i₂ := eq26480 X0
       grind)
    | exact superpose eq26480 eq26855
    | exact resolve eq26855 eq26480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26480 eq26855
  have eq27204 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op X1 (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 (τ X0) X1
       have i₂ := eq26910 X0
       grind)
    | exact superpose eq26910 eq76
    | exact resolve eq76 eq26910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26910
  have eq27409 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq26918 X0
       grind)
    | exact superpose eq26918 eq68
    | exact resolve eq68 eq26918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27456 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq26918 X0
       grind)
    | exact superpose eq26918 eq9
    | exact resolve eq9 eq26918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29191 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (σ (M.op X0 X0))) (M.op X1 (σ (σ X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27456 (σ X0) X1
       have i₂ := eq26918 X0
       grind)
    | exact superpose eq26918 eq27456
    | exact resolve eq27456 eq26918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27456
  have eq35113 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5448
       have i₂ := eq26918 x
       grind)
    | exact superpose eq26918 eq5448
    | exact resolve eq5448 eq26918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5448
  have eq35114 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq35113
       have i₂ := eq26918 y
       grind)
    | exact superpose eq26918 eq35113
    | exact resolve eq35113 eq26918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26918 eq35113
  have eq36253 : (M.op y y) = (τ (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq35114
       grind)
    | exact superpose eq35114 eq10
    | exact resolve eq10 eq35114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35114
  have eq36382 : y = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq36253
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq36253
    | exact resolve eq36253 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36253
  have eq36383 : (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq36382
  have eq36432 : (M.op x x) = (τ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq36383
       grind)
    | exact superpose eq36383 eq10
    | exact resolve eq10 eq36383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36383
  have eq36556 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36432
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq36432
    | exact resolve eq36432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36432
  have eq36557 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq36556
  have eq36581 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq36557
       grind)
    | exact superpose eq36557 eq76
    | exact resolve eq76 eq36557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq36693 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq846 y y x
       have i₂ := eq36557
       grind)
    | exact superpose eq36557 eq846
    | exact resolve eq846 eq36557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36557
  have eq36719 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq36693 X0
       have i₂ := eq93 y X0
       grind)
    | exact superpose eq93 eq36693
    | exact resolve eq36693 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq36693
  have eq41156 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq36581 X0
       have i₂ := eq36719 X0
       grind)
    | exact superpose eq36719 eq36581
    | exact resolve eq36581 eq36719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36581 eq36719
  have eq41289 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq41156 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41156
  have eq41315 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 x
       have i₂ := eq41289 X0
       grind)
    | exact superpose eq41289 eq68
    | (have j1 := eq41289 x
       grind)
    | exact resolve eq68 eq41289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq41371 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq27409 x
       have i₂ := eq41289 X0
       grind)
    | exact superpose eq41289 eq27409
    | (have j1 := eq41289 X0
       grind)
    | exact resolve eq27409 eq41289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27409 eq41289
  have eq41529 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq41315 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41315
  have eq41530 : x = (M.op x y) := by grind
  clear eq41529
  have eq45111 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq41371 X0
       grind)
    | exact superpose eq41371 eq16
    | (have j1 := eq41371 X0
       grind)
    | exact resolve eq16 eq41371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41371
  have eq45211 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq45111 X0
       have i₂ := eq41530
       grind)
    | exact superpose eq41530 eq45111
    | (have j0 := eq45111 X0
       grind)
    | exact resolve eq45111 eq41530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41530 eq45111
  have eq45212 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq45211 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45211
  have eq45886 : ∀ X0 : G, (M.op X0 (M.op (τ y) (M.op X0 (τ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq27204 y X0
       have i₂ := eq45212 y
       grind)
    | exact superpose eq45212 eq27204
    | exact resolve eq27204 eq45212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27204
  have eq45963 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X1 y) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq846 y X1 X0
       have i₂ := eq45212 X0
       grind)
    | exact superpose eq45212 eq846
    | exact resolve eq846 eq45212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq46151 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45963 X0 X0
       have i₂ := eq45212 X0
       grind)
    | exact superpose eq45212 eq45963
    | exact resolve eq45963 eq45212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45963
  have eq68938 : ∀ X0 : G, (M.op X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq45886 X0
       have i₂ := eq46151 X0 (τ y)
       grind)
    | exact superpose eq46151 eq45886
    | exact resolve eq45886 eq46151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45886
  have eq69019 : ∀ X0 : G, (M.op X0 (M.op (σ (σ (τ y))) (M.op X0 (σ (σ (τ y)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29191 (τ y) X0
       have i₂ := eq68938 (τ y)
       grind)
    | exact superpose eq68938 eq29191
    | exact resolve eq29191 eq68938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29191 eq68938
  have eq69311 : ∀ X0 : G, (M.op X0 (σ (σ (τ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq69019 X0
       have i₂ := eq46151 X0 (σ (σ (τ y)))
       grind)
    | exact superpose eq46151 eq69019
    | exact resolve eq69019 eq46151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46151 eq69019
  have eq69381 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq69311 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq69311
    | exact resolve eq69311 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69311
  have eq69733 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69381 (σ x)
       grind)
    | exact superpose eq69381 eq16
    | exact resolve eq16 eq69381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69381
  have eq69745 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq69733
       have i₂ := eq45212 x
       grind)
    | exact superpose eq45212 eq69733
    | exact resolve eq69733 eq45212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45212 eq69733
  have eq69746 : False := by grind
  exact eq69746

/-- `Equation880`: `x = y ◇ ((x ◇ y) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pxy_pxy_pyy_pxy_Equation880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq14 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X0 X2
       have j1 := eq14 X0 X2
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq45 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq29 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq29 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq38 X1 X1
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
  have eq49 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq24 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq24 X1 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq24 X0 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq24 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq39 X0 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq39 X0 X1
       grind)
    | (have r₁ := eq48 X1 X1
       have r₂ := eq39 X1 X1
       grind)
    | exact resolve eq48 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq48
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq49 X1 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq49 X0 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq49 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq20 (σ X0)
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq55
    | exact resolve eq55 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq86 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X0)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq139
    | (have j0 := eq139 X0 X1
       grind)
    | exact resolve eq139 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq214 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq19
    | (have j1 := eq45 X0 X1
       grind)
    | exact resolve eq19 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq288 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0) (σ X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq19
    | exact resolve eq19 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq291 X0
       have i₂ := eq56 (M.op X0 X0)
       grind)
    | exact superpose eq56 eq291
    | exact resolve eq291 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq312 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq288 X0
       have i₂ := eq56 (M.op X0 X0)
       grind)
    | exact superpose eq56 eq288
    | exact resolve eq288 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq374 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq53 (σ x) (σ y) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq53 (σ x) X0 (σ y)
       grind)
    | exact superpose eq53 eq16
    | (have j1 := eq53 (σ x) (σ y) (σ y)
       grind)
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq416 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq374 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq374
    | (have j0 := eq374 X0
       grind)
    | exact resolve eq374 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq597 : ∀ X0 : G, (σ (M.op x y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k (σ x) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq416 (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))
       have i₂ := eq9 X0 (σ x)
       grind)
    | exact superpose eq9 eq416
    | (have r₁ := eq416 (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) (σ x)))
       have r₂ := eq9 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq416 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq1036 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) = (M.op (M.op X1 X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (σ X0) X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq86
    | exact resolve eq86 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1114 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) (σ x)))) := by
    first
    | (have j0 := eq597 (σ (M.op x y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq1115 : (σ (M.op x y)) = (k (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x x)))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1114
       have i₂ := eq1036 x (σ (M.op x y))
       grind)
    | exact superpose eq1036 eq1114
    | exact resolve eq1114 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036 eq1114
  have eq1118 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x x)))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1115
       have i₂ := eq56 (M.op x y)
       grind)
    | exact superpose eq56 eq1115
    | exact resolve eq1115 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1119 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op (M.op x x) (M.op y y))) (σ (M.op x x)))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1118
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq1118
    | exact resolve eq1118 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq1118
  have eq4425 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op (M.op x x) (M.op x x))) (σ (M.op x x)))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1119
       have i₂ := eq214 x y
       grind)
    | exact superpose eq214 eq1119
    | (have j1 := eq214 x y
       grind)
    | exact resolve eq1119 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq1119
  have eq4477 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4425
       have i₂ := eq309 x
       grind)
    | exact superpose eq309 eq4425
    | exact resolve eq4425 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq4425
  have eq4505 : (σ (M.op x y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4477
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq4477
    | exact resolve eq4477 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4477
  have eq4507 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4505
       have i₂ := eq20 x
       grind)
    | exact superpose eq20 eq4505
    | exact resolve eq4505 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4505
  have eq5695 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4507
       have i₂ := eq52 x y
       grind)
    | exact superpose eq52 eq4507
    | (have j1 := eq52 x y
       grind)
    | exact resolve eq4507 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq4507
  have eq5717 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq160 x y
       grind)
    | (have r₁ := eq5695
       have r₂ := eq160 x y
       grind)
    | exact resolve eq5695 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq5695
  have eq14529 : (σ x) = (M.op (σ y) (M.op (σ (M.op y y)) (σ (M.op y y)))) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq5717
       grind)
    | exact superpose eq5717 eq9
    | exact resolve eq9 eq5717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5717
  have eq14620 : (σ x) = (M.op (σ y) (σ (M.op (M.op y y) (M.op y y)))) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq14529
       have i₂ := eq56 (M.op y y)
       grind)
    | exact superpose eq56 eq14529
    | exact resolve eq14529 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14529
  have eq14654 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14620
       have i₂ := eq312 y
       grind)
    | exact superpose eq312 eq14620
    | exact resolve eq14620 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq14620
  have eq20981 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq172 x y
       have i₂ := eq14654
       grind)
    | exact superpose eq14654 eq172
    | exact resolve eq172 eq14654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq14654
  have eq20987 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20981
       have r₂ := eq16
       grind)
    | exact resolve eq20981 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20981
  have eq30751 : (M.op y y) = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq20987
       grind)
    | exact superpose eq20987 eq10
    | exact resolve eq10 eq20987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20987
  have eq30823 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30751
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq30751
    | exact resolve eq30751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30751
  have eq40612 : (M.op x y) = (τ (σ (M.op x x))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq30823
       grind)
    | exact superpose eq30823 eq10
    | exact resolve eq10 eq30823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30823
  have eq40725 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40612
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq40612
    | exact resolve eq40612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40612
  have eq49815 : y = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq40725
       grind)
    | exact superpose eq40725 eq9
    | exact resolve eq9 eq40725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40725
  have eq49935 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49815
       have i₂ := eq9 x y
       grind)
    | exact superpose eq9 eq49815
    | exact resolve eq49815 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49815
  have eq50538 : y = (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19 x y
       have i₂ := eq49935
       grind)
    | exact superpose eq49935 eq19
    | exact resolve eq19 eq49935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49935
  have eq50620 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50538
       have i₂ := eq19 x x
       grind)
    | exact superpose eq19 eq50538
    | exact resolve eq50538 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq50538
  have eq50621 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq50620
  have eq51071 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq50621
       grind)
    | exact superpose eq50621 eq10
    | exact resolve eq10 eq50621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50621
  have eq51182 : x = y ∨ x = y := by
    first
    | (have i₁ := eq51071
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq51071
    | exact resolve eq51071 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51071
  have eq51183 : x = y := by grind
  clear eq51182
  have eq55995 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51183
       grind)
    | exact superpose eq51183 eq16
    | exact resolve eq16 eq51183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51183
  have eq56022 : False := by grind
  exact eq56022
