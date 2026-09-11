import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
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
  have eq275 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq275 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq278 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq276 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq276 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq276 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq289 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq278 (σ X0)
       grind)
    | exact superpose eq278 eq15
    | exact resolve eq15 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq278 (τ X0)
       grind)
    | exact superpose eq278 eq32
    | exact resolve eq32 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq302 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq295 X0
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq295
    | exact resolve eq295 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq308 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq289 X0
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq289
    | exact resolve eq289 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq289
  have eq354 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq308 X0
       grind)
    | exact superpose eq308 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq308 X0
       grind)
    | exact superpose eq308 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq357 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq354 X0 X1
       have j1 := eq356 X0 X1
       grind)
    | (have r₁ := eq354 X0 X1
       have r₂ := eq356 X0 X1
       grind)
    | exact resolve eq354 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq356
  have eq371 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq374 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq371 X0 X1
       have j1 := eq373 X0 X1
       grind)
    | (have r₁ := eq371 X0 X1
       have r₂ := eq373 X0 X1
       grind)
    | exact resolve eq371 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq373
  have eq419 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq357 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq357
    | exact resolve eq357 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq357 x (σ y)
       grind)
    | exact superpose eq357 eq16
    | (have j1 := eq357 x (σ y)
       grind)
    | exact resolve eq16 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq440 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq423
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq423
    | exact resolve eq423 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq445 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq419 X1 X0
       grind)
    | exact superpose eq419 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq419 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq419 X0 X1
       grind)
    | exact resolve eq13 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq459 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq445 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq463 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq459 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq459 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq459 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq476 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq463 X1 (σ X0)
       grind)
    | exact superpose eq463 eq23
    | (have j1 := eq463 X1 (σ X0)
       grind)
    | exact resolve eq23 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq494 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq463 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq374 X0 X1
       grind)
    | exact superpose eq374 eq19
    | (have j1 := eq374 X0 X1
       grind)
    | exact resolve eq19 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1895 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X1)
       have i₂ := eq476 X1 (σ X0)
       grind)
    | exact superpose eq476 eq29
    | (have j1 := eq476 X1 (σ X0)
       grind)
    | exact resolve eq29 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq476
  have eq1906 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1895 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1895
    | (have j0 := eq1895 X0 X1
       grind)
    | exact resolve eq1895 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895
  have eq1920 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1906 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1906
    | (have j0 := eq1906 X0 X1
       grind)
    | exact resolve eq1906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906
  have eq1929 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1920 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1920
    | (have j0 := eq1920 X0 X1
       grind)
    | exact resolve eq1920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq2005 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq1929 X0 X1
       grind)
    | exact superpose eq1929 eq11
    | (have j1 := eq1929 X0 X1
       grind)
    | exact resolve eq11 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929
  have eq2048 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2005 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2005
    | (have j0 := eq2005 X1 (τ X0)
       grind)
    | exact resolve eq2005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2058 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2005 y x
       grind)
    | exact superpose eq2005 eq16
    | (have j1 := eq2005 y x
       grind)
    | exact resolve eq16 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2139 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2048 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq2048
    | (have j0 := eq2048 X0 X1
       grind)
    | exact resolve eq2048 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2048
  have eq2160 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2058
       have i₂ := eq463 y x
       grind)
    | exact superpose eq463 eq2058
    | (have j1 := eq463 y x
       grind)
    | exact resolve eq2058 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq2058
  have eq2161 : y = (M.op x y) ∨ y = (k y x) := by grind
  clear eq2160
  have eq2162 : y = (k y x) := by
    first
    | (have j1 := eq494 y x
       grind)
    | (have r₁ := eq2161
       have r₂ := eq494 y x
       grind)
    | exact resolve eq2161 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq2161
  have eq2244 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op (τ X1) X0) = X0 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X1 X0
       have i₂ := eq2139 X1 X0
       grind)
    | exact superpose eq2139 eq374
    | (have j0 := eq374 X1 X0
       have j1 := eq2139 X1 X0
       grind)
    | exact resolve eq374 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq2139
  have eq2257 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2244 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq2364 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2257 X1 (σ X0)
       grind)
    | exact superpose eq2257 eq15
    | (have j1 := eq2257 X1 (σ X0)
       grind)
    | exact resolve eq15 eq2257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq2404 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2364 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2364
    | (have j0 := eq2364 X0 X1
       grind)
    | exact resolve eq2364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2364
  have eq2554 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2404 x y
       grind)
    | exact superpose eq2404 eq16
    | (have j1 := eq2404 x y
       grind)
    | exact resolve eq16 eq2404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2404
  have eq2631 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2554
       have i₂ := eq2162
       grind)
    | exact superpose eq2162 eq2554
    | exact resolve eq2554 eq2162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq3027 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1102 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1102
    | exact resolve eq1102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq3114 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3027 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3027
    | (have j0 := eq3027 X0 X1
       grind)
    | exact resolve eq3027 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3027
  have eq3155 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3114 x y
       have i₂ := eq2162
       grind)
    | exact superpose eq2162 eq3114
    | (have j0 := eq3114 x y
       grind)
    | exact resolve eq3114 eq2162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq3224 : y = (M.op x y) := by
    first
    | (have r₁ := eq3155
       have r₂ := eq2631
       grind)
    | exact resolve eq3155 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631 eq3155
  have eq6441 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq440
       have i₂ := eq3224
       grind)
    | exact superpose eq3224 eq440
    | exact resolve eq440 eq3224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq6444 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq6441
  have eq6446 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6444
       have i₂ := eq2162
       grind)
    | exact superpose eq2162 eq6444
    | exact resolve eq6444 eq2162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162 eq6444
  have eq6452 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6446
       grind)
    | exact superpose eq6446 eq16
    | exact resolve eq16 eq6446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6446
  have eq6496 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6452
       have i₂ := eq3224
       grind)
    | exact superpose eq3224 eq6452
    | exact resolve eq6452 eq3224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3224 eq6452
  have eq6497 : False := by grind
  exact eq6497

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation221 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq52 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq172 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq52 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq13
    | (have j0 := eq13 (k (σ X1) (σ X0)) (M.op (σ X0) (σ X1))
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq185 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq191 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq185
    | (have j0 := eq185 X0 X1
       grind)
    | exact resolve eq185 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq192 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq366 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq192
    | exact resolve eq192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq192 x y
       grind)
    | exact superpose eq192 eq16
    | (have j1 := eq192 x y
       grind)
    | exact resolve eq16 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq390 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq366
    | (have j0 := eq366 X0 X1
       grind)
    | exact resolve eq366 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq366
  have eq395 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq390 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq390
    | exact resolve eq390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq506 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq372
       have i₂ := eq395 x y
       grind)
    | exact superpose eq395 eq372
    | (have j1 := eq395 (σ x) (σ y)
       grind)
    | (have r₁ := eq372
       have r₂ := eq395 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq372
       have r₂ := eq395 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq372 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq395
  have eq509 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq506
  have eq511 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq509
       grind)
    | exact superpose eq509 eq10
    | exact resolve eq10 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq546 : x = y ∨ x = y := by
    first
    | (have i₁ := eq511
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq511
    | exact resolve eq511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq547 : x = y := by grind
  clear eq546
  have eq590 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq16
    | exact resolve eq16 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq591 : False := by grind
  exact eq591

/-- `Equation2274`: `x = (x ◇ (y ◇ (z ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_pxy_pyx_Equation2274 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2274 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2274.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X0))) X1) = X0 := by
    intro X0 X1 X2
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
  clear eq35
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
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
  have eq58 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X1 (M.op x X0)))
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 X1) (M.op X3 X0)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 (M.op (M.op X2 X1) (M.op X3 X0))) X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq86 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq128 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq397 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (M.op X2 (M.op (M.op x X0) (M.op x X2))) X1 (M.op X0 X2)
       have i₂ := eq59 X2 X0 x x
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq59
  have eq399 : ∀ X0 : G, x = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq397 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq397
    | (have j0 := eq397 y x X0
       grind)
    | exact resolve eq397 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq397
    | (have j0 := eq397 (σ y) (σ x) X0
       grind)
    | exact resolve eq397 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq397 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq397
    | (have j0 := eq397 x X0 y
       grind)
    | exact resolve eq397 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq551 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq9433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq9434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9433
    | exact resolve eq9433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9433
  have eq9445 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq9434
       have r₂ := eq27
       grind)
    | exact resolve eq9434 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9434
  have eq9447 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9445
    | exact resolve eq9445 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9445
  have eq9476 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9447 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9447
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9447
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq9447
       grind)
    | exact resolve eq13 eq9447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9447
  have eq9492 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq9476
  have eq9576 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9492 eq96
    | exact resolve eq96 eq9492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq9492
  have eq9602 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq9576
    | exact resolve eq9576 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9576
  have eq9605 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq9602
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq9602
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq9602
       have r₂ := eq13 y x
       grind)
    | exact resolve eq9602 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9602
  have eq9616 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq551 x y
       have i₂ := eq9605
       grind)
    | exact superpose eq9605 eq551
    | (have j0 := eq551 x y
       grind)
    | exact resolve eq551 eq9605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9618 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq9605
       grind)
    | exact superpose eq9605 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq9605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9605
  have eq9619 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9618
  have eq9621 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9616
  have eq9624 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9619
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9619
    | exact resolve eq9619 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9619
  have eq9625 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9624
  have eq9627 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9621
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9621
    | exact resolve eq9621 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9621
  have eq9640 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9627
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9627
    | exact resolve eq9627 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9627
  have eq9644 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9640
    | exact resolve eq9640 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9640
  have eq9645 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9644
  have eq9649 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9645
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9645
    | exact resolve eq9645 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9645
  have eq9654 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9649
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9649
    | exact resolve eq9649 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9649
  have eq9716 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq9625
       grind)
    | exact superpose eq9625 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9625
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9625
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9625
       grind)
    | exact resolve eq12 eq9625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9625
  have eq9735 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9716
  have eq9739 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9735
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9735
    | exact resolve eq9735 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9735
  have eq9740 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9739
  have eq9741 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9740
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9740
    | exact resolve eq9740 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9740
  have eq9783 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9654 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9654
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9654
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9654
       grind)
    | exact resolve eq12 eq9654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9654
  have eq9802 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9783
  have eq9806 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9802
    | exact resolve eq9802 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9802
  have eq9807 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9806
  have eq9808 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9807
    | exact resolve eq9807 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9807
  have eq9900 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq9741
       grind)
    | exact superpose eq9741 eq44
    | exact resolve eq44 eq9741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9741
  have eq9922 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9900
    | exact resolve eq9900 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9900
  have eq10052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9922 eq9808
    | exact resolve eq9808 eq9922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9808 eq9922
  have eq10058 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10052
  have eq10060 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10058
       have r₂ := eq27
       grind)
    | exact resolve eq10058 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10058
  have eq10072 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10060 eq51
    | (have r₁ := eq51
       have r₂ := eq10060
       grind)
    | exact resolve eq51 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq10060
  have eq10085 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10072
  have eq10092 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10085 eq55
    | exact resolve eq55 eq10085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq10085
  have eq10122 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq10092
    | exact resolve eq10092 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10092
  have eq10126 : y = (k x y) := by
    first
    | (have r₁ := eq10122
       have r₂ := eq50
       grind)
    | exact resolve eq10122 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq10122
  have eq10129 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq10126
       grind)
    | exact superpose eq10126 eq44
    | exact resolve eq44 eq10126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10139 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq551 y x
       have i₂ := eq10126
       grind)
    | exact superpose eq10126 eq551
    | (have j0 := eq551 y x
       grind)
    | exact resolve eq551 eq10126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq10141 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq10126
       grind)
    | exact superpose eq10126 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq10126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10142 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq10141
  have eq10144 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10139
  have eq10147 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10142
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10142
    | exact resolve eq10142 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10142
  have eq10149 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10144
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10144
    | exact resolve eq10144 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10144
  have eq10158 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq10129
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10129
    | exact resolve eq10129 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10129
  have eq10161 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10149
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10149
    | exact resolve eq10149 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10149
  have eq10165 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10161
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10161
    | exact resolve eq10161 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10161
  have eq10169 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10165
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10165
    | exact resolve eq10165 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10165
  have eq10173 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10169
    | exact resolve eq10169 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10169
  have eq11105 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq399 x
       have i₂ := eq10147
       grind)
    | exact superpose eq10147 eq399
    | exact resolve eq399 eq10147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq11107 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq409 y
       have i₂ := eq10147
       grind)
    | exact superpose eq10147 eq409
    | exact resolve eq409 eq10147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq11108 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq10147
       grind)
    | exact superpose eq10147 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq10147
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10147
       grind)
    | exact resolve eq12 eq10147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10147
  have eq11127 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq11108
  have eq11131 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11127
    | exact resolve eq11127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11127
  have eq11132 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq11131
  have eq11133 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11132
       have i₂ := eq10126
       grind)
    | exact superpose eq10126 eq11132
    | exact resolve eq11132 eq10126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10126 eq11132
  have eq11134 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11133
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11133
    | exact resolve eq11133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq11133
  have eq11199 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq12445 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq11134 eq11105
    | exact resolve eq11105 eq11134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11105
  have eq12464 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12445
       have r₂ := eq11199
       grind)
    | exact resolve eq12445 eq11199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12445
  have eq12465 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq11134 eq11107
    | exact resolve eq11107 eq11134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11107 eq11134
  have eq12496 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12465
       have r₂ := eq11199
       grind)
    | exact resolve eq12465 eq11199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12465
  have eq13156 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12464
       have i₂ := eq12496
       grind)
    | exact superpose eq12496 eq12464
    | exact resolve eq12464 eq12496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12464 eq12496
  have eq13179 : x = y ∨ x = (M.op x y) := by grind
  clear eq13156
  have eq13182 : x = (M.op x y) := by
    first
    | (have r₁ := eq13179
       have r₂ := eq11199
       grind)
    | exact resolve eq13179 eq11199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11199 eq13179
  have eq13185 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13182 eq20
    | exact resolve eq20 eq13182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq13202 : (σ (k x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13182 eq128
    | exact resolve eq128 eq13182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq13182
  have eq13285 : (k (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq13202
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq13202
    | exact resolve eq13202 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq13202
  have eq13299 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13185
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13185
    | exact resolve eq13185 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13185
  have eq13307 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq10158 eq13285
    | exact resolve eq13285 eq10158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10158 eq13285
  have eq13314 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13299 eq26
    | exact resolve eq26 eq13299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq13389 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13299 eq10173
    | exact resolve eq10173 eq13299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10173
  have eq13392 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq13389
       have r₂ := eq27
       grind)
    | exact resolve eq13389 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13389
  have eq13506 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq13392 eq400
    | exact resolve eq400 eq13392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13507 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13392 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq13392
       grind)
    | exact resolve eq12 eq13392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13528 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq13507
  have eq13530 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13314 eq13528
    | exact resolve eq13528 eq13314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13528
  have eq13531 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq13299 eq13506
    | exact resolve eq13506 eq13299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13506
  have eq13533 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq13530
       have r₂ := eq27
       grind)
    | exact resolve eq13530 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13530
  have eq13534 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13314 eq13533
    | exact resolve eq13533 eq13314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13314 eq13533
  have eq13535 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13307 eq13534
    | exact resolve eq13534 eq13307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13307 eq13534
  have eq13537 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq13535 eq27
    | exact resolve eq27 eq13535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq13612 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq13535 eq13531
    | exact resolve eq13531 eq13535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13531
  have eq13701 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13612 eq400
    | exact resolve eq400 eq13612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq13612
  have eq13721 : (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq13535 eq13701
    | exact resolve eq13701 eq13535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13535 eq13701
  have eq13723 : (σ x) = (σ y) := by
    first
    | exact superpose eq13392 eq13721
    | exact resolve eq13721 eq13392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13392 eq13721
  have eq13725 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13299 eq13723
    | exact resolve eq13723 eq13299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13299 eq13723
  have eq13726 : False := by grind
  exact eq13726

/-- `Equation2278`: `x = (x ◇ (y ◇ (z ◇ y))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_pxy_pyx_Equation2278 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2278 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2278.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X1))) X1) = X0 := by
    intro X0 X1 X2
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
  clear eq35
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
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
  have eq58 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 (M.op x X2)))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq86 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq128 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq219 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 y X0 x
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq219 (M.op X1 (M.op sF0 X0))
       have i₂ := eq58 X0 X1 sF0
       grind)
    | exact superpose eq58 eq219
    | exact resolve eq219 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq219 eq58
    | exact resolve eq58 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq353 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq234 eq14
    | exact resolve eq14 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq423 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq235 eq58
    | exact resolve eq58 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq235
  have eq582 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq780 : ∀ X0 : G, x = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq423 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq423
    | (have j0 := eq423 y x X0
       grind)
    | exact resolve eq423 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq423
    | (have j0 := eq423 (σ y) (σ x) X0
       grind)
    | exact resolve eq423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq12053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq12054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12053
    | exact resolve eq12053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12053
  have eq12065 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq12054
       have r₂ := eq27
       grind)
    | exact resolve eq12054 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12054
  have eq12067 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12065
    | exact resolve eq12065 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12065
  have eq12183 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12067 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12067
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq12067
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12067
       grind)
    | exact resolve eq13 eq12067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12067
  have eq12211 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq12183
  have eq12234 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12211 eq96
    | exact resolve eq96 eq12211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq12211
  have eq12260 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq12234
    | exact resolve eq12234 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12234
  have eq12263 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq12260
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq12260
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq12260
       have r₂ := eq13 y x
       grind)
    | exact resolve eq12260 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12260
  have eq12385 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq582 x y
       have i₂ := eq12263
       grind)
    | exact superpose eq12263 eq582
    | (have j0 := eq582 x y
       grind)
    | exact resolve eq582 eq12263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12387 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq12263
       grind)
    | exact superpose eq12263 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq12263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12263
  have eq12388 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12387
  have eq12390 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12385
  have eq12393 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12388
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12388
    | exact resolve eq12388 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12388
  have eq12394 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12393
  have eq12396 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12390
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12390
    | exact resolve eq12390 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12390
  have eq12409 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12396
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12396
    | exact resolve eq12396 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12396
  have eq12413 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12409
    | exact resolve eq12409 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12409
  have eq12414 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12413
  have eq12418 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12414
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12414
    | exact resolve eq12414 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12414
  have eq12423 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12418
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12418
    | exact resolve eq12418 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12418
  have eq12429 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq12394
       grind)
    | exact superpose eq12394 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12394
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12394
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12394
       grind)
    | exact resolve eq12 eq12394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12394
  have eq12458 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12429
  have eq12464 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12458
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12458
    | exact resolve eq12458 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12458
  have eq12465 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12464
  have eq12467 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12465
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12465
    | exact resolve eq12465 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12465
  have eq12559 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12423 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12423
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12423
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12423
       grind)
    | exact resolve eq12 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12423
  have eq12589 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12559
  have eq12599 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12589
    | exact resolve eq12589 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12589
  have eq12600 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12599
  have eq12604 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12600
    | exact resolve eq12600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12600
  have eq12945 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq12467
       grind)
    | exact superpose eq12467 eq44
    | exact resolve eq44 eq12467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12467
  have eq12967 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12945
    | exact resolve eq12945 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12945
  have eq13681 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12967 eq12604
    | exact resolve eq12604 eq12967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12604 eq12967
  have eq13687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13681
  have eq13689 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13687
       have r₂ := eq27
       grind)
    | exact resolve eq13687 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13687
  have eq13701 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13689 eq51
    | (have r₁ := eq51
       have r₂ := eq13689
       grind)
    | exact resolve eq51 eq13689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq13689
  have eq13726 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13701
  have eq13852 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13726 eq55
    | exact resolve eq55 eq13726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq13726
  have eq13882 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq13852
    | exact resolve eq13852 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13852
  have eq13886 : y = (k x y) := by
    first
    | (have r₁ := eq13882
       have r₂ := eq50
       grind)
    | exact resolve eq13882 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq13882
  have eq13889 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq13886
       grind)
    | exact superpose eq13886 eq44
    | exact resolve eq44 eq13886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13899 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq582 y x
       have i₂ := eq13886
       grind)
    | exact superpose eq13886 eq582
    | (have j0 := eq582 y x
       grind)
    | exact resolve eq582 eq13886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq13901 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq13886
       grind)
    | exact superpose eq13886 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq13886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13902 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq13901
  have eq13904 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13899
  have eq13907 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13902
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13902
    | exact resolve eq13902 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13902
  have eq13909 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13904
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13904
    | exact resolve eq13904 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13904
  have eq13918 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13889
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13889
    | exact resolve eq13889 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13889
  have eq13921 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13909
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13909
    | exact resolve eq13909 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13909
  have eq13925 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13921
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13921
    | exact resolve eq13921 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13921
  have eq13929 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13925
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13925
    | exact resolve eq13925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13925
  have eq13933 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13929
    | exact resolve eq13929 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13929
  have eq14069 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq780 x
       have i₂ := eq13907
       grind)
    | exact superpose eq13907 eq780
    | exact resolve eq780 eq13907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq14071 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq353 y
       have i₂ := eq13907
       grind)
    | exact superpose eq13907 eq353
    | exact resolve eq353 eq13907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq14072 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq13907
       grind)
    | exact superpose eq13907 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13907
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13907
       grind)
    | exact resolve eq12 eq13907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13907
  have eq14101 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq14072
  have eq14107 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14101
    | exact resolve eq14101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14101
  have eq14108 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq14107
  have eq14110 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14108
       have i₂ := eq13886
       grind)
    | exact superpose eq13886 eq14108
    | exact resolve eq14108 eq13886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13886 eq14108
  have eq14112 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14110
    | exact resolve eq14110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq14110
  have eq14195 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq14530 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14112 eq14069
    | exact resolve eq14069 eq14112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14069
  have eq14555 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14530
       have r₂ := eq14195
       grind)
    | exact resolve eq14530 eq14195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14530
  have eq14557 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14112 eq14071
    | exact resolve eq14071 eq14112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14071 eq14112
  have eq14606 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14557
       have r₂ := eq14195
       grind)
    | exact resolve eq14557 eq14195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14557
  have eq14902 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14555
       have i₂ := eq14606
       grind)
    | exact superpose eq14606 eq14555
    | exact resolve eq14555 eq14606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14555 eq14606
  have eq14932 : x = y ∨ x = (M.op x y) := by grind
  clear eq14902
  have eq14936 : x = (M.op x y) := by
    first
    | (have r₁ := eq14932
       have r₂ := eq14195
       grind)
    | exact resolve eq14932 eq14195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14195 eq14932
  have eq14940 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq14936 eq20
    | exact resolve eq20 eq14936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq14957 : (σ (k x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq14936 eq128
    | exact resolve eq128 eq14936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq14936
  have eq15066 : (k (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq14957
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq14957
    | exact resolve eq14957 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq14957
  have eq15080 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14940
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14940
    | exact resolve eq14940 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14940
  have eq15092 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13918 eq15066
    | exact resolve eq15066 eq13918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13918 eq15066
  have eq15100 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15080 eq26
    | exact resolve eq26 eq15080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq15180 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15080 eq13933
    | exact resolve eq13933 eq15080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13933
  have eq15183 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq15180
       have r₂ := eq27
       grind)
    | exact resolve eq15180 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15180
  have eq15330 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq15183 eq783
    | exact resolve eq783 eq15183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15331 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15183 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq15183
       grind)
    | exact resolve eq12 eq15183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15361 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq15331
  have eq15373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15100 eq15361
    | exact resolve eq15361 eq15100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15361
  have eq15374 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq15080 eq15330
    | exact resolve eq15330 eq15080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15330
  have eq15383 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq15373
       have r₂ := eq27
       grind)
    | exact resolve eq15373 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15373
  have eq15388 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15100 eq15383
    | exact resolve eq15383 eq15100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15100 eq15383
  have eq15392 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15092 eq15388
    | exact resolve eq15388 eq15092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15092 eq15388
  have eq15668 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq15392 eq27
    | exact resolve eq27 eq15392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq15774 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq15392 eq15374
    | exact resolve eq15374 eq15392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15374
  have eq15851 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15774 eq783
    | exact resolve eq783 eq15774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq15774
  have eq15880 : (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq15392 eq15851
    | exact resolve eq15851 eq15392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15392 eq15851
  have eq15884 : (σ x) = (σ y) := by
    first
    | exact superpose eq15183 eq15880
    | exact resolve eq15880 eq15183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15183 eq15880
  have eq15886 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15080 eq15884
    | exact resolve eq15884 eq15080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15080 eq15884
  have eq15888 : False := by grind
  exact eq15888

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq51 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq164 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq171 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq164 X0 X1
       have j1 := eq51 X0 X1
       grind)
    | (have r₁ := eq164 X0 X1
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq164 X1 X1
       have r₂ := eq51 X1 X1
       grind)
    | exact resolve eq164 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq164
  have eq404 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq171 (σ X1) (σ X0)
       grind)
    | exact superpose eq171 eq15
    | exact resolve eq15 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq404 X0 X1
       have i₂ := eq171 X1 X0
       grind)
    | exact superpose eq171 eq404
    | exact resolve eq404 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq404
  have eq414 : False := by grind
  exact eq414

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxy_pxx_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq39
    | exact resolve eq39 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq174 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq91
    | exact resolve eq91 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq206 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 X0 X1 X2
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq174
    | (have j0 := eq174 X0 X1 X2
       grind)
    | exact resolve eq174 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq174
  have eq3518 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 (σ X1)) (σ X2)) ≠ (M.op (k X0 (σ X1)) X3) ∨ (M.op (k X0 (σ X1)) (σ X2)) = (k (k X0 (σ X1)) X3) ∨ (M.op X3 X3) = (M.op X3 (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k X0 (σ X1)) X1
       have i₂ := eq206 X0 X1 X2
       grind)
    | exact superpose eq206 eq13
    | (have j0 := eq13 (k X0 (σ X1)) X3
       have j1 := eq206 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq206 X0 X1 X2
       grind)
    | exact resolve eq13 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq161838 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (M.op (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3518 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3518
  have eq161870 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq161838 X0 X1 X2
       have j1 := eq12 (k X0 (σ X1)) (σ X2)
       grind)
    | (have r₁ := eq161838 X0 X1 X2
       have r₂ := eq12 (k X0 (σ X1)) (σ X2)
       grind)
    | exact resolve eq161838 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161838
  have eq161973 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq161870 X0 X1 X2
       have j1 := eq78 X2 (k X0 (σ X1))
       grind)
    | (have r₁ := eq161870 X0 X1 X0
       have r₂ := eq78 X0 (k X0 (σ X1))
       grind)
    | exact resolve eq161870 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq161870
  have eq162051 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq161973 X0 X1 X2
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq161973
    | (have j0 := eq161973 X0 X1 X2
       grind)
    | exact resolve eq161973 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq161973
  have eq162052 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq162051 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162051
  have eq162495 : ∀ X0 X1 X2 : G, (k (σ (k (τ X0) X1)) X2) = (M.op (k X0 (σ X1)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k (τ X0) X1)
       have i₂ := eq162052 X0 X1 (τ X2)
       grind)
    | exact superpose eq162052 eq18
    | exact resolve eq18 eq162052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq162052
  have eq162844 : ∀ X0 X1 X2 : G, (k (σ (k (τ X0) X1)) X2) = (M.op (k X0 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162495 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq162495
    | exact resolve eq162495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162495
  have eq163106 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) X2) = (M.op (k X0 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162844 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq162844
    | exact resolve eq162844 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq162844
  have eq163345 : ∀ X0 X1 X2 : G, (k (k X1 X0) X2) = (M.op (k X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163106 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq163106
    | exact resolve eq163106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163417 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) X1) = (M.op (M.op (σ X0) (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq163106 (σ X1) X1 x
       have i₂ := eq32 (σ X1)
       grind)
    | exact superpose eq32 eq163106
    | exact resolve eq163106 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163106
  have eq163985 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq163417 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq163417
    | exact resolve eq163417 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163417
  have eq165400 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq163345 X0 X0 x
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq163345
    | exact resolve eq163345 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq165476 : ∀ X0 X1 X2 : G, (k (τ (k X0 X1)) X2) = (M.op (τ (k X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163345 (τ X0) (τ X1) X2
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq163345
    | exact resolve eq163345 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq165502 : ∀ X0 X1 X2 X3 : G, (k (M.op (k X0 X1) X2) X3) = (M.op (M.op (k X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq163345 X2 (k X1 X0) X2
       have i₂ := eq163345 X0 X1 X2
       grind)
    | exact superpose eq163345 eq163345
    | exact resolve eq163345 eq163345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165744 : ∀ X0 X1 X2 : G, (k (τ (k X0 X1)) X2) = (τ (M.op (k X0 X1) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (k X0 X1) X2
       have i₂ := eq163345 X1 X0 (σ X2)
       grind)
    | exact superpose eq163345 eq23
    | exact resolve eq23 eq163345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq163345
  have eq174821 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ X1)) = (τ (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (M.op X0 X0) X1
       have i₂ := eq163985 X0 X1
       grind)
    | exact superpose eq163985 eq29
    | exact resolve eq29 eq163985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq174874 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq163985 X0 (σ X1)
       grind)
    | exact superpose eq163985 eq15
    | exact resolve eq15 eq163985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163985
  have eq175228 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174874 X0 X1
       have i₂ := eq165400 X0 X1
       grind)
    | exact superpose eq165400 eq174874
    | exact resolve eq174874 eq165400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174874
  have eq175272 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ X1)) = (τ (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174821 X0 X1
       have i₂ := eq165400 X0 (τ X1)
       grind)
    | exact superpose eq165400 eq174821
    | exact resolve eq174821 eq165400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174821
  have eq180709 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op X0 X0) X1)) X2) = (M.op (τ (M.op (M.op X0 X0) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165476 (M.op X0 X0) X1 X2
       have i₂ := eq165400 X0 X1
       grind)
    | exact superpose eq165400 eq165476
    | exact resolve eq165476 eq165400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165476
  have eq190379 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op X0 X0) X1)) X2) = (τ (M.op (M.op (M.op X0 X0) X1) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165744 (M.op X0 X0) X1 X2
       have i₂ := eq165400 X0 X1
       grind)
    | exact superpose eq165400 eq165744
    | exact resolve eq165744 eq165400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165744
  have eq191077 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X0 X0) X1)) X2) = (τ (M.op (M.op (M.op X0 X0) X1) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq190379 X0 X1 X2
       have i₂ := eq180709 X0 X1 X2
       grind)
    | exact superpose eq180709 eq190379
    | exact resolve eq190379 eq180709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180709 eq190379
  have eq226702 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X3) = (k (M.op (M.op (M.op X0 X0) X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq165502 (M.op X0 X0) X1 X2 X3
       have i₂ := eq165400 X0 X1
       grind)
    | exact superpose eq165400 eq165502
    | exact resolve eq165502 eq165400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165400 eq165502
  have eq375540 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (M.op (M.op X1 X1) (M.op (σ X0) (M.op (M.op X1 X1) (σ X0))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq191077 X1 (M.op (σ X0) (M.op (M.op X1 X1) (σ X0))) X0
       have i₂ := eq9 (σ X0) (M.op X1 X1)
       grind)
    | exact superpose eq9 eq191077
    | exact resolve eq191077 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191077
  have eq375915 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X1 X1) (M.op (σ X0) (M.op (M.op X1 X1) (σ X0))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq375540 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq375540
    | exact resolve eq375540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375540
  have eq429058 : ∀ X0 X1 : G, (M.op (τ (M.op (σ (M.op X0 X0)) (M.op (σ X1) (M.op (σ (M.op X0 X0)) (σ X1))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq375915 X0 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq375915
    | exact resolve eq375915 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq375915
  have eq429488 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (τ (M.op (σ X1) (M.op (σ (M.op X0 X0)) (σ X1))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq429058 X0 X1
       have i₂ := eq175272 X0 (M.op (σ X1) (M.op (σ (M.op X0 X0)) (σ X1)))
       grind)
    | exact superpose eq175272 eq429058
    | exact resolve eq429058 eq175272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175272 eq429058
  have eq429606 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (τ (M.op (σ X1) (σ (M.op (M.op X0 X0) X1))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq429488 X0 X1
       have i₂ := eq175228 X0 X1
       grind)
    | exact superpose eq175228 eq429488
    | exact resolve eq429488 eq175228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175228 eq429488
  have eq617427 : ∀ X0 X2 : G, (k X0 X2) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq226702 X0 (τ (M.op (σ x) (σ (M.op (M.op X0 X0) x)))) x x
       have i₂ := eq429606 X0 x
       grind)
    | exact superpose eq429606 eq226702
    | exact resolve eq226702 eq429606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226702 eq429606
  have eq620283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq617427 (σ X0) (σ X1)
       grind)
    | exact superpose eq617427 eq15
    | exact resolve eq15 eq617427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620695 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq620283 X0 X1
       have i₂ := eq617427 X0 X1
       grind)
    | exact superpose eq617427 eq620283
    | exact resolve eq620283 eq617427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617427 eq620283
  have eq634182 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq620695 x y
       grind)
    | exact superpose eq620695 eq16
    | (have r₁ := eq16
       have r₂ := eq620695 x y
       grind)
    | exact resolve eq16 eq620695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620695
  have eq634418 : False := by grind
  exact eq634418

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxy_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq83
  have eq177 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq191 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq177 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq198 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq191 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq191 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq191 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq210 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       have j1 := eq79 X0 (σ X1)
       grind)
    | (have r₁ := eq198 X0 X1
       have r₂ := eq79 X0 (σ X1)
       grind)
    | exact resolve eq198 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq198
  have eq217 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq210
    | (have j0 := eq210 X0 X1
       grind)
    | exact resolve eq210 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq218 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq217 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq223 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq218
    | exact resolve eq218 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq218 x y
       grind)
    | exact superpose eq218 eq16
    | exact resolve eq16 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq290 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq223 X0 (τ X1)
       grind)
    | exact superpose eq223 eq17
    | exact resolve eq17 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq223
  have eq308 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq290
    | exact resolve eq290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq317 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq308
    | exact resolve eq308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq334 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq234
       have i₂ := eq317 x y
       grind)
    | exact superpose eq317 eq234
    | exact resolve eq234 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq317
  have eq335 : False := by grind
  exact eq335

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
       have j1 := eq14 X0 X1
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq32 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq40
    | (have j0 := eq40 X0 X1
       grind)
    | exact resolve eq40 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq41
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq47 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq47
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       have j1 := eq49 X0 X1
       grind)
    | (have r₁ := eq90 X0 X1
       have r₂ := eq49 X0 X1
       grind)
    | (have r₁ := eq90 X0 X0
       have r₂ := eq49 X0 X0
       grind)
    | exact resolve eq90 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq90
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq94 (σ X0) (σ X1)
       grind)
    | exact superpose eq94 eq15
    | exact resolve eq15 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq211
    | exact resolve eq211 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq211
  have eq220 : False := by grind
  exact eq220
