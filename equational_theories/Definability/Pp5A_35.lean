import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxx_pyy_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq64 (M.op X0 X1)
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq99
    | exact resolve eq99 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq361 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq361
    | (have j0 := eq361 X0 X1
       grind)
    | (have r₁ := eq361 X0 X0
       have r₂ := eq64 X0
       grind)
    | exact resolve eq361 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq379 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq374
    | (have j0 := eq374 X0 X1
       grind)
    | (have r₁ := eq374 X0 X0
       have r₂ := eq64 X0
       grind)
    | exact resolve eq374 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq403 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  clear eq19
  have eq407 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq434 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 X1
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq407
    | (have j0 := eq407 X0 X1
       grind)
    | exact resolve eq407 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq437 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq404 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq404
    | (have j0 := eq404 X0 X1
       grind)
    | exact resolve eq404 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq438 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq403
    | (have j0 := eq403 X0 X1
       grind)
    | exact resolve eq403 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq462 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X1
       have i₂ := eq64 (σ X1)
       grind)
    | exact superpose eq64 eq434
    | (have j0 := eq434 X0 X1
       grind)
    | exact resolve eq434 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq465 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq437 X0 X1
       have i₂ := eq64 (τ X1)
       grind)
    | exact superpose eq64 eq437
    | (have j0 := eq437 X0 X1
       grind)
    | exact resolve eq437 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq466 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 X1
       have i₂ := eq64 (σ X1)
       grind)
    | exact superpose eq64 eq438
    | (have j0 := eq438 X0 X1
       grind)
    | exact resolve eq438 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq575 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq465
    | exact resolve eq465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq599 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq575
    | (have j0 := eq575 X0 X1
       grind)
    | exact resolve eq575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq615 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq599 X1 X0
       grind)
    | exact superpose eq599 eq10
    | (have j1 := eq599 X1 X0
       grind)
    | exact resolve eq10 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq615 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq615
    | (have j0 := eq615 X0 X1
       grind)
    | exact resolve eq615 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq2207 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq466
    | exact resolve eq466 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2224 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq466 (σ x) y
       grind)
    | exact superpose eq466 eq16
    | (have j1 := eq466 (σ y) x
       grind)
    | (have r₁ := eq16
       have r₂ := eq466 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq2242 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2224
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2224
    | exact resolve eq2224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq2244 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2207 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq2207
    | (have j0 := eq2207 X0 X1
       grind)
    | exact resolve eq2207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2207
  have eq2258 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq379 X0 X1
       have i₂ := eq2244 X1 X0
       grind)
    | exact superpose eq2244 eq379
    | (have j0 := eq379 X0 X1
       have j1 := eq2244 X1 X0
       grind)
    | (have r₁ := eq379 X1 X0
       have r₂ := eq2244 X0 X1
       grind)
    | (have r₁ := eq379 X1 X1
       have r₂ := eq2244 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq379 X0 X1
       have r₂ := eq2244 X0 (M.op X0 X1)
       grind)
    | exact resolve eq379 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq2244
  have eq2269 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2258 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2258
  have eq2270 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2302 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq2270 (σ X0) X1
       grind)
    | exact superpose eq2270 eq29
    | (have j1 := eq2270 (σ X0) X1
       grind)
    | exact resolve eq29 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq2305 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq2270 X0 X1
       grind)
    | exact superpose eq2270 eq11
    | (have j1 := eq2270 X0 X1
       grind)
    | exact resolve eq11 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq2363 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2305 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq2305
    | (have j0 := eq2305 X0 X1
       grind)
    | exact resolve eq2305 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305
  have eq2413 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq2363 (τ X0) X1
       grind)
    | exact superpose eq2363 eq18
    | (have j1 := eq2363 (τ X0) X1
       grind)
    | exact resolve eq18 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2363
  have eq3910 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq2302 X1 (σ X0)
       grind)
    | exact superpose eq2302 eq23
    | (have j1 := eq2302 X1 (σ X0)
       grind)
    | exact resolve eq23 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2302
  have eq3961 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3910 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3910
    | (have j0 := eq3910 X0 X1
       grind)
    | exact resolve eq3910 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3910
  have eq3993 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3961 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3961
    | (have j0 := eq3961 X0 X1
       grind)
    | exact resolve eq3961 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3961
  have eq4000 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3993 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3993
    | (have j0 := eq3993 X0 X1
       grind)
    | exact resolve eq3993 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3993
  have eq4003 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2413 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2413
    | exact resolve eq2413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq4055 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4003 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4003
    | (have j0 := eq4003 X0 X1
       grind)
    | exact resolve eq4003 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4003
  have eq4190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4000 X1 X0
       grind)
    | exact superpose eq4000 eq11
    | (have j1 := eq4000 X1 X0
       grind)
    | exact resolve eq11 eq4000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4000
  have eq4835 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4190 x y
       grind)
    | exact superpose eq4190 eq16
    | (have j1 := eq4190 x y
       grind)
    | exact resolve eq16 eq4190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4190
  have eq4884 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4835
       have i₂ := eq649 x y
       grind)
    | exact superpose eq649 eq4835
    | (have j1 := eq649 x y
       grind)
    | (have r₁ := eq4835
       have r₂ := eq649 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4835
       have r₂ := eq649 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4835 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq4835
  have eq4892 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4884
  have eq4915 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4892
       grind)
    | exact superpose eq4892 eq16
    | exact resolve eq16 eq4892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4892
  have eq4916 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4915
       have i₂ := eq64 (σ x)
       grind)
    | exact superpose eq64 eq4915
    | exact resolve eq4915 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915
  have eq4917 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4916
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq4916
    | exact resolve eq4916 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4916
  have eq4918 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq4917
  have eq4922 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67 x y
       have i₂ := eq4918
       grind)
    | exact superpose eq4918 eq67
    | exact resolve eq67 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4933 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  have eq4947 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4922
       have i₂ := eq4918
       grind)
    | exact superpose eq4918 eq4922
    | exact resolve eq4922 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918 eq4922
  have eq4962 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq4947
  have eq4966 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4962
       have r₂ := eq4933
       grind)
    | exact resolve eq4962 eq4933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933 eq4962
  have eq15365 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2242
       have i₂ := eq4966
       grind)
    | exact superpose eq4966 eq2242
    | exact resolve eq2242 eq4966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242 eq4966
  have eq15383 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq15365
  have eq15384 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq15383
  have eq15392 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15384
       grind)
    | exact superpose eq15384 eq10
    | exact resolve eq10 eq15384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15384
  have eq15449 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq15392
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15392
    | exact resolve eq15392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15392
  have eq15451 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15449
       grind)
    | exact superpose eq15449 eq16
    | exact resolve eq16 eq15449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15449
  have eq15454 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq15451
       have i₂ := eq64 (σ x)
       grind)
    | exact superpose eq64 eq15451
    | exact resolve eq15451 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15451
  have eq15455 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq15454
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq15454
    | exact resolve eq15454 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15454
  have eq15456 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq15455
  have eq15479 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq15456
       grind)
    | exact superpose eq15456 eq11
    | exact resolve eq11 eq15456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15456
  have eq15579 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15479
       grind)
    | exact superpose eq15479 eq16
    | exact resolve eq16 eq15479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15588 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq67 (σ x) (σ y)
       have i₂ := eq15479
       grind)
    | exact superpose eq15479 eq67
    | exact resolve eq67 eq15479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq15671 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq15579
       have i₂ := eq4055 x y
       grind)
    | exact superpose eq4055 eq15579
    | (have j1 := eq4055 x y
       grind)
    | (have r₁ := eq15579
       have r₂ := eq4055 x y
       grind)
    | (have r₁ := eq15579
       have r₂ := eq4055 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq15579
       have r₂ := eq4055 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq15579 eq4055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4055
  have eq15672 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq15579
       have i₂ := eq599 y x
       grind)
    | exact superpose eq599 eq15579
    | (have j1 := eq599 y x
       grind)
    | (have r₁ := eq15579
       have r₂ := eq599 y x
       grind)
    | (have r₁ := eq15579
       have r₂ := eq599 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq15579
       have r₂ := eq599 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq15579 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq15673 : x = y ∨ x = (M.op x y) := by grind
  clear eq15672
  have eq15674 : x = y ∨ y = (k x y) := by grind
  clear eq15671
  have eq15684 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15579
       have i₂ := eq15673
       grind)
    | exact superpose eq15673 eq15579
    | exact resolve eq15579 eq15673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15673
  have eq15685 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15684
       have i₂ := eq100 x
       grind)
    | exact superpose eq100 eq15684
    | exact resolve eq15684 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15684
  have eq15690 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15685
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq15685
    | exact resolve eq15685 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15685
  have eq15691 : x = (M.op x y) := by grind
  clear eq15690
  have eq15863 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq15579
       have i₂ := eq15674
       grind)
    | exact superpose eq15674 eq15579
    | exact resolve eq15579 eq15674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15674
  have eq15867 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq15863
       have i₂ := eq100 x
       grind)
    | exact superpose eq100 eq15863
    | exact resolve eq15863 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq15863
  have eq15872 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq15867
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq15867
    | exact resolve eq15867 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq15867
  have eq15873 : y = (k x y) := by grind
  clear eq15872
  have eq15887 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq15579
       have i₂ := eq15873
       grind)
    | exact superpose eq15873 eq15579
    | exact resolve eq15579 eq15873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15579
  have eq15903 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq15887
       have i₂ := eq15691
       grind)
    | exact superpose eq15691 eq15887
    | exact resolve eq15887 eq15691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15691 eq15887
  have eq16050 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq15588
       have i₂ := eq462 x (k x y)
       grind)
    | exact superpose eq462 eq15588
    | (have j1 := eq462 x (k x y)
       grind)
    | exact resolve eq15588 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq15588
  have eq16095 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16050
       have i₂ := eq15873
       grind)
    | exact superpose eq15873 eq16050
    | exact resolve eq16050 eq15873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16050
  have eq16096 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq16095
  have eq16108 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16096
       have i₂ := eq15873
       grind)
    | exact superpose eq15873 eq16096
    | exact resolve eq16096 eq15873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16096
  have eq16119 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16108
       have i₂ := eq15479
       grind)
    | exact superpose eq15479 eq16108
    | exact resolve eq16108 eq15479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15479 eq16108
  have eq16120 : (σ x) = (σ (k x y)) := by grind
  clear eq16119
  have eq16128 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16120
       have i₂ := eq15873
       grind)
    | exact superpose eq15873 eq16120
    | exact resolve eq16120 eq15873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15873 eq16120
  have eq16134 : False := by grind
  exact eq16134

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_y_pyy_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    grind
  have eq40 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq36 (M.op X0 X1)
       grind)
    | exact superpose eq36 eq9
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | (have r₁ := eq47 X0 X0
       have r₂ := eq36 X0
       grind)
    | exact resolve eq47 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | (have r₁ := eq51 X0 X0
       have r₂ := eq36 X0
       grind)
    | exact resolve eq51 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq88 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  clear eq19
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq93 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq36 (σ X1)
       grind)
    | exact superpose eq36 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq97 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq36 (τ X1)
       grind)
    | exact superpose eq36 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq99 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq120 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq128 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 X1
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq120
    | (have j0 := eq120 X0 X1
       grind)
    | exact resolve eq120 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq131 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq128
    | (have j0 := eq128 X0 X1
       grind)
    | exact resolve eq128 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq132
    | (have j0 := eq132 X0 X1
       grind)
    | exact resolve eq132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq524 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq146
    | exact resolve eq146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq785 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq819 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq785 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq785
    | (have j0 := eq785 X0 X1
       grind)
    | exact resolve eq785 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq4078 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k x (τ (σ y))) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131 x (σ y)
       grind)
    | exact superpose eq131 eq16
    | (have j1 := eq131 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq131 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4083 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq53
    | (have j0 := eq53 (σ X0) X1
       have j1 := eq131 X0 X1
       grind)
    | (have r₁ := eq53 (σ X0) X1
       have r₂ := eq131 X0 X1
       grind)
    | (have r₁ := eq53 (σ X0) X1
       have r₂ := eq131 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq53 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq131
  have eq4100 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4083 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4083
  have eq4101 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100
  have eq4109 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4078
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4078
    | exact resolve eq4078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4078
  have eq5361 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4101 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4101
    | exact resolve eq4101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5411 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq4101 X1 (σ X0)
       grind)
    | exact superpose eq4101 eq23
    | (have j1 := eq4101 X0 (σ X1)
       grind)
    | exact resolve eq23 eq4101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4101
  have eq5476 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5411 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5411
    | (have j0 := eq5411 X0 X1
       grind)
    | exact resolve eq5411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5411
  have eq5487 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5361 X0 X1
       have i₂ := eq99 X1 X0
       grind)
    | exact superpose eq99 eq5361
    | (have j0 := eq5361 X0 X1
       grind)
    | exact resolve eq5361 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq5361
  have eq5510 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5476 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5476
    | (have j0 := eq5476 X0 X1
       grind)
    | exact resolve eq5476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476
  have eq5517 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5510 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5510
    | (have j0 := eq5510 X0 X1
       grind)
    | exact resolve eq5510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5510
  have eq5547 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq5487 X0 X1
       grind)
    | exact superpose eq5487 eq11
    | (have j1 := eq5487 X0 X1
       grind)
    | exact resolve eq11 eq5487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5487
  have eq5657 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5547 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq5547
    | (have j0 := eq5547 X0 X1
       grind)
    | exact resolve eq5547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5547
  have eq5796 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq5657 (τ X0) X1
       grind)
    | exact superpose eq5657 eq18
    | (have j1 := eq5657 (τ X0) X1
       grind)
    | exact resolve eq18 eq5657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5657
  have eq6242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq5517 X1 X0
       grind)
    | exact superpose eq5517 eq11
    | (have j1 := eq5517 X1 X0
       grind)
    | exact resolve eq11 eq5517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5517
  have eq7349 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6242 x y
       grind)
    | exact superpose eq6242 eq16
    | (have j1 := eq6242 x y
       grind)
    | exact resolve eq16 eq6242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6242
  have eq7723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7349
       have i₂ := eq524 y x
       grind)
    | exact superpose eq524 eq7349
    | (have j1 := eq524 y x
       grind)
    | (have r₁ := eq7349
       have r₂ := eq524 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq7349
       have r₂ := eq524 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq7349 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq7349
  have eq7728 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7723
  have eq8001 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7728
       grind)
    | exact superpose eq7728 eq16
    | exact resolve eq16 eq7728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7728
  have eq8002 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8001
       have i₂ := eq36 (σ x)
       grind)
    | exact superpose eq36 eq8001
    | exact resolve eq8001 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8001
  have eq8003 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8002
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq8002
    | exact resolve eq8002 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8002
  have eq8004 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq8003
  have eq8009 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x y
       have i₂ := eq8004
       grind)
    | exact superpose eq8004 eq40
    | exact resolve eq40 eq8004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8021 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  have eq8172 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8009
       have i₂ := eq8004
       grind)
    | exact superpose eq8004 eq8009
    | exact resolve eq8009 eq8004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8004 eq8009
  have eq8191 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq8172
  have eq8195 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8191
       have r₂ := eq8021
       grind)
    | exact resolve eq8191 eq8021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8021 eq8191
  have eq9484 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5796 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5796
    | exact resolve eq5796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5796
  have eq9610 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9484 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9484
    | (have j0 := eq9484 X0 X1
       grind)
    | exact resolve eq9484 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9484
  have eq36321 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4109
       have i₂ := eq8195
       grind)
    | exact superpose eq8195 eq4109
    | exact resolve eq4109 eq8195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109 eq8195
  have eq36322 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq36321
  have eq36323 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq36322
  have eq36336 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq36323
       grind)
    | exact superpose eq36323 eq10
    | exact resolve eq10 eq36323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36323
  have eq36445 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq36336
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq36336
    | exact resolve eq36336 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36336
  have eq36697 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36445
       grind)
    | exact superpose eq36445 eq16
    | exact resolve eq16 eq36445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36445
  have eq36698 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq36697
       have i₂ := eq36 (σ x)
       grind)
    | exact superpose eq36 eq36697
    | exact resolve eq36697 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36697
  have eq36699 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq36698
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq36698
    | exact resolve eq36698 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36698
  have eq36700 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq36699
  have eq36729 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq36700
       grind)
    | exact superpose eq36700 eq11
    | exact resolve eq11 eq36700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36700
  have eq37303 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36729
       grind)
    | exact superpose eq36729 eq16
    | exact resolve eq16 eq36729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37330 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq40 (σ x) (σ y)
       have i₂ := eq36729
       grind)
    | exact superpose eq36729 eq40
    | exact resolve eq40 eq36729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq37444 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq37303
       have i₂ := eq9610 x y
       grind)
    | exact superpose eq9610 eq37303
    | (have j1 := eq9610 x y
       grind)
    | (have r₁ := eq37303
       have r₂ := eq9610 x y
       grind)
    | (have r₁ := eq37303
       have r₂ := eq9610 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq37303
       have r₂ := eq9610 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq37303 eq9610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9610
  have eq37445 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq37303
       have i₂ := eq819 y x
       grind)
    | exact superpose eq819 eq37303
    | (have j1 := eq819 y x
       grind)
    | (have r₁ := eq37303
       have r₂ := eq819 y x
       grind)
    | (have r₁ := eq37303
       have r₂ := eq819 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq37303
       have r₂ := eq819 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq37303 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq37446 : x = y ∨ x = (M.op x y) := by grind
  clear eq37445
  have eq37447 : x = y ∨ y = (k x y) := by grind
  clear eq37444
  have eq37758 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37303
       have i₂ := eq37446
       grind)
    | exact superpose eq37446 eq37303
    | exact resolve eq37303 eq37446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37446
  have eq37759 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37758
       have i₂ := eq38 x
       grind)
    | exact superpose eq38 eq37758
    | exact resolve eq37758 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37758
  have eq37763 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37759
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq37759
    | exact resolve eq37759 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37759
  have eq37764 : x = (M.op x y) := by grind
  clear eq37763
  have eq38214 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq37303
       have i₂ := eq37447
       grind)
    | exact superpose eq37447 eq37303
    | exact resolve eq37303 eq37447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37447
  have eq38218 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq38214
       have i₂ := eq38 x
       grind)
    | exact superpose eq38 eq38214
    | exact resolve eq38214 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq38214
  have eq38222 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq38218
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq38218
    | exact resolve eq38218 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38218
  have eq38223 : y = (k x y) := by grind
  clear eq38222
  have eq38419 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq37303
       have i₂ := eq38223
       grind)
    | exact superpose eq38223 eq37303
    | exact resolve eq37303 eq38223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37303
  have eq38459 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq38419
       have i₂ := eq37764
       grind)
    | exact superpose eq37764 eq38419
    | exact resolve eq38419 eq37764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37764 eq38419
  have eq39123 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq37330
       have i₂ := eq96 x (k x y)
       grind)
    | exact superpose eq96 eq37330
    | (have j1 := eq96 x (k x y)
       grind)
    | exact resolve eq37330 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq37330
  have eq39190 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq39123
       have i₂ := eq38223
       grind)
    | exact superpose eq38223 eq39123
    | exact resolve eq39123 eq38223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39123
  have eq39191 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq39190
  have eq39206 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq39191
       have i₂ := eq38223
       grind)
    | exact superpose eq38223 eq39191
    | exact resolve eq39191 eq38223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39191
  have eq39218 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq39206
       have i₂ := eq36729
       grind)
    | exact superpose eq36729 eq39206
    | exact resolve eq39206 eq36729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36729 eq39206
  have eq39219 : (σ x) = (σ (k x y)) := by grind
  clear eq39218
  have eq39225 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq39219
       have i₂ := eq38223
       grind)
    | exact superpose eq38223 eq39219
    | exact resolve eq39219 eq38223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38223 eq39219
  have eq39231 : False := by grind
  exact eq39231

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxy_pyx_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq15
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq95
    | exact resolve eq95 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq95
  have eq248 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106 x y
       grind)
    | exact superpose eq106 eq16
    | (have r₁ := eq16
       have r₂ := eq106 x y
       grind)
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq256 : False := by grind
  exact eq256

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_pxy_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X0) := by
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
  have eq397 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 (M.op X1 X1) (M.op (σ X0) X1)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq398 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq424 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq828 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq424 x y
       grind)
    | exact superpose eq424 eq16
    | (have j1 := eq424 x y
       grind)
    | exact resolve eq16 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq424 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq2986 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq398 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq398
    | exact resolve eq398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq3035 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2986 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2986
    | (have j0 := eq2986 X0 X1
       grind)
    | exact resolve eq2986 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq3240 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq397 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq397
    | exact resolve eq397 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq3300 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3240 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq3240
    | (have j0 := eq3240 X0 X1
       grind)
    | exact resolve eq3240 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3240
  have eq3314 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq3300 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq3300 X0 X1
       grind)
    | exact superpose eq3300 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq3300 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq3300 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3300 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq3300 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300
  have eq3343 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3314 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3314
  have eq3386 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
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
  have eq3501 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
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
  have eq3521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3501 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3501
    | (have j0 := eq3501 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3501 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3541 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq3501 (τ X0) X1
       grind)
    | exact superpose eq3501 eq19
    | (have j1 := eq3501 (τ X0) X1
       grind)
    | exact resolve eq19 eq3501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3501
  have eq3679 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3521 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq3521
    | (have j0 := eq3521 X0 X1
       grind)
    | exact resolve eq3521 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521
  have eq3935 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3541 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3541
    | exact resolve eq3541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3541
  have eq3992 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3935 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3935
    | (have j0 := eq3935 X0 X1
       grind)
    | exact resolve eq3935 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3935
  have eq11278 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3679 y x
       grind)
    | exact superpose eq3679 eq16
    | (have j1 := eq3679 y x
       grind)
    | exact resolve eq16 eq3679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11366 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq11278
       have i₂ := eq3992 x y
       grind)
    | exact superpose eq3992 eq11278
    | (have j1 := eq3992 x y
       grind)
    | (have r₁ := eq11278
       have r₂ := eq3992 x y
       grind)
    | (have r₁ := eq11278
       have r₂ := eq3992 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11278
       have r₂ := eq3992 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11278 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq11367 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11278
       have i₂ := eq3035 x y
       grind)
    | exact superpose eq3035 eq11278
    | (have j1 := eq3035 x y
       grind)
    | (have r₁ := eq11278
       have r₂ := eq3035 x y
       grind)
    | (have r₁ := eq11278
       have r₂ := eq3035 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11278
       have r₂ := eq3035 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11278 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035 eq11278
  have eq11368 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq11367
  have eq11369 : x = y ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq11366
  have eq11497 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11368
       grind)
    | exact superpose eq11368 eq16
    | exact resolve eq16 eq11368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11368
  have eq11498 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11497
       have r₂ := eq78 x
       grind)
    | exact resolve eq11497 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11497
  have eq11525 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11369
       grind)
    | exact superpose eq11369 eq16
    | exact resolve eq16 eq11369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11369
  have eq11526 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq11525
       have r₂ := eq78 x
       grind)
    | exact resolve eq11525 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11525
  have eq11531 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq835 x y
       have i₂ := eq11526
       grind)
    | exact superpose eq11526 eq835
    | (have j0 := eq835 x y
       grind)
    | exact resolve eq835 eq11526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11526
  have eq11548 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq11531
  have eq11549 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq11548
  have eq11557 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3679 y x
       have i₂ := eq11549
       grind)
    | exact superpose eq11549 eq3679
    | (have j0 := eq3679 y x
       grind)
    | exact resolve eq3679 eq11549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3679 eq11549
  have eq11573 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq11557
  have eq11585 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11573
       grind)
    | exact superpose eq11573 eq10
    | exact resolve eq10 eq11573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11573
  have eq11645 : x = y ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11585
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11585
    | exact resolve eq11585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11585
  have eq11647 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11645
       grind)
    | exact superpose eq11645 eq16
    | exact resolve eq16 eq11645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11645
  have eq11648 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq11647
       have r₂ := eq78 x
       grind)
    | exact resolve eq11647 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11647
  have eq11656 : (M.op y y) = (τ (σ (M.op x y))) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq11648
       grind)
    | exact superpose eq11648 eq10
    | exact resolve eq10 eq11648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11648
  have eq11716 : (M.op x y) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11656
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq11656
    | exact resolve eq11656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11656
  have eq11719 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11716
       grind)
    | exact superpose eq11716 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq11716
       grind)
    | exact resolve eq12 eq11716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11716
  have eq12646 : (M.op x y) = (k y x) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have j0 := eq11719 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11719
  have eq12661 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq828
       have i₂ := eq12646
       grind)
    | exact superpose eq12646 eq828
    | exact resolve eq828 eq12646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq12646
  have eq12678 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq12661
  have eq12681 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq835 x y
       grind)
    | (have r₁ := eq12678
       have r₂ := eq835 x y
       grind)
    | exact resolve eq12678 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq12678
  have eq12685 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12681
       grind)
    | exact superpose eq12681 eq16
    | exact resolve eq16 eq12681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12681
  have eq12717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12685
       have i₂ := eq11498
       grind)
    | exact superpose eq11498 eq12685
    | (have r₁ := eq12685
       have r₂ := eq11498
       grind)
    | exact resolve eq12685 eq11498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11498
  have eq12722 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq12717
  have eq12723 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq12722
  have eq12725 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq12723
       have r₂ := eq12685
       grind)
    | exact resolve eq12723 eq12685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12685 eq12723
  have eq12726 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12725
       grind)
    | exact superpose eq12725 eq16
    | exact resolve eq16 eq12725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12727 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12725
       grind)
    | exact superpose eq12725 eq10
    | exact resolve eq10 eq12725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12725
  have eq12789 : x = y := by
    first
    | (have i₁ := eq12727
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12727
    | exact resolve eq12727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12727
  have eq12790 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12726
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq12726
    | exact resolve eq12726 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq12726
  have eq12791 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12790
       have i₂ := eq12789
       grind)
    | exact superpose eq12789 eq12790
    | exact resolve eq12790 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12789 eq12790
  have eq12792 : False := by grind
  exact eq12792

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyy_pxy_pyy_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq41
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq44 X1 X1
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq44 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq44
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq120 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq115 X0 X1
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq115 X0 X0
       have r₂ := eq46 X0 X0
       grind)
    | exact resolve eq115 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq115
  have eq269 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq120 (σ X0) (σ X1)
       grind)
    | exact superpose eq120 eq15
    | exact resolve eq15 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq269 X0 X1
       have i₂ := eq120 X0 X1
       grind)
    | exact superpose eq120 eq269
    | exact resolve eq269 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq269
  have eq278 : False := by grind
  exact eq278

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq266 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq275 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq281 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq275 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq275 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq282 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq266
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq283 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq282
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq282
    | exact resolve eq282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq404 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq281 X0 (τ X1)
       grind)
    | exact superpose eq281 eq17
    | (have j1 := eq281 X0 (τ X1)
       grind)
    | exact resolve eq17 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq410 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq281 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq404 (τ X0) X1
       grind)
    | exact superpose eq404 eq18
    | (have j1 := eq404 (τ X0) X1
       grind)
    | exact resolve eq18 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq404
  have eq776 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq771 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq771
    | (have j0 := eq771 X0 X1
       grind)
    | exact resolve eq771 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq789 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq776 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq776
    | (have j0 := eq776 X0 X1
       grind)
    | exact resolve eq776 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq792 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq789 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq789
    | (have j0 := eq789 X0 X1
       grind)
    | exact resolve eq789 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq855 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq792 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq792
    | (have j0 := eq792 X1 (σ X0)
       grind)
    | exact resolve eq792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq1245 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X0
       have i₂ := eq281 X0 (σ X0)
       grind)
    | exact superpose eq281 eq855
    | (have j0 := eq855 X1 X0
       have j1 := eq281 X0 (σ X1)
       grind)
    | exact resolve eq855 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq855
  have eq1275 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1245 X0 X1
       have j1 := eq410 (σ X1) X0
       grind)
    | (have r₁ := eq1245 X1 X1
       have r₂ := eq410 (σ X1) X1
       grind)
    | exact resolve eq1245 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq1245
  have eq1442 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1275 (σ X0) X1
       grind)
    | exact superpose eq1275 eq22
    | (have j1 := eq1275 (σ X0) X1
       grind)
    | exact resolve eq22 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1275
  have eq1449 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1442 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1442
    | (have j0 := eq1442 X0 X1
       grind)
    | exact resolve eq1442 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442
  have eq1465 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1449 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1449
    | (have j0 := eq1449 X0 X1
       grind)
    | exact resolve eq1449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq1474 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1465 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1465
    | (have j0 := eq1465 X0 X1
       grind)
    | exact resolve eq1465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1558 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1474 x y
       grind)
    | exact superpose eq1474 eq16
    | (have j1 := eq1474 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1474 x y
       grind)
    | exact resolve eq16 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq1578 : x = (k y x) := by grind
  clear eq1558
  have eq1839 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq283
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq283
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq283 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1840 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq1839
  have eq1841 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1840
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1840 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq1842 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1841
       have i₂ := eq1578
       grind)
    | exact superpose eq1578 eq1841
    | exact resolve eq1841 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq1843 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1842
       have i₂ := eq1578
       grind)
    | exact superpose eq1578 eq1842
    | exact resolve eq1842 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq1844 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq283
       have i₂ := eq1843
       grind)
    | exact superpose eq1843 eq283
    | exact resolve eq283 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq1843
  have eq1854 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1844
  have eq1855 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1854
       have i₂ := eq1578
       grind)
    | exact superpose eq1578 eq1854
    | exact resolve eq1854 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1854
  have eq1856 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1855
  have eq1858 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1856
       grind)
    | exact superpose eq1856 eq16
    | exact resolve eq16 eq1856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq1883 : (σ x) ≠ (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1858
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1858
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1858 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1884 : x = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq1883
  have eq1886 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1884
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1884 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884
  have eq1887 : x = (M.op x y) := by
    first
    | (have i₁ := eq1886
       have i₂ := eq1578
       grind)
    | exact superpose eq1578 eq1886
    | exact resolve eq1886 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578 eq1886
  have eq1888 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1858
       have i₂ := eq1887
       grind)
    | exact superpose eq1887 eq1858
    | exact resolve eq1858 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858 eq1887
  have eq1900 : False := by grind
  exact eq1900

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq375 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
  have eq390 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq378 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq392 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq390 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq390 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq390 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq390 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq390 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq404 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq391 (M.op X1 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq391 X0 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq391 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq391 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq407 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq375
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq375 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq409 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq404 X0 X1
       have j1 := eq392 X0 X1
       grind)
    | (have r₁ := eq404 X0 X1
       have r₂ := eq392 X0 X1
       grind)
    | (have r₁ := eq404 X1 X0
       have r₂ := eq392 X0 X1
       grind)
    | (have r₁ := eq404 X1 X1
       have r₂ := eq392 (k X1 X1) X1
       grind)
    | exact resolve eq404 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq404
  have eq411 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq407
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq539 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq409 X0 (τ X1)
       grind)
    | exact superpose eq409 eq17
    | (have j1 := eq409 X0 (τ X1)
       grind)
    | exact resolve eq17 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq546 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq409 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq411
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq411
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq411 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq776
  have eq778 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq777
       have r₂ := eq12 y x
       grind)
    | exact resolve eq777 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq797 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq539 (τ X0) X1
       grind)
    | exact superpose eq539 eq18
    | (have j1 := eq539 (τ X0) X1
       grind)
    | exact resolve eq18 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq539
  have eq802 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq797 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq797
    | (have j0 := eq797 X0 X1
       grind)
    | exact resolve eq797 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq815 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq802 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq802
    | (have j0 := eq802 X0 X1
       grind)
    | exact resolve eq802 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq818 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq815 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq815
    | (have j0 := eq815 X0 X1
       grind)
    | exact resolve eq815 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq879 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq818 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq818
    | (have j0 := eq818 X1 (σ X0)
       grind)
    | exact resolve eq818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq1243 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq879 X0 X0
       have i₂ := eq409 X0 (σ X0)
       grind)
    | exact superpose eq409 eq879
    | (have j0 := eq879 X1 X0
       have j1 := eq409 X0 (σ X1)
       grind)
    | exact resolve eq879 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq879
  have eq1273 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1243 X0 X1
       have j1 := eq546 (σ X1) X0
       grind)
    | (have r₁ := eq1243 X1 X1
       have r₂ := eq546 (σ X1) X1
       grind)
    | exact resolve eq1243 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq1243
  have eq1440 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1273 (σ X0) X1
       grind)
    | exact superpose eq1273 eq22
    | (have j1 := eq1273 (σ X0) X1
       grind)
    | exact resolve eq22 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1273
  have eq1447 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1440 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1440
    | (have j0 := eq1440 X0 X1
       grind)
    | exact resolve eq1440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq1463 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1447 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1447
    | (have j0 := eq1447 X0 X1
       grind)
    | exact resolve eq1447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq1472 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1463 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1463
    | (have j0 := eq1463 X0 X1
       grind)
    | exact resolve eq1463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq1556 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1472 x y
       grind)
    | exact superpose eq1472 eq16
    | (have j1 := eq1472 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1472 x y
       grind)
    | exact resolve eq16 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1576 : x = (k y x) := by grind
  clear eq1556
  have eq1954 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq778
       have i₂ := eq1576
       grind)
    | exact superpose eq1576 eq778
    | exact resolve eq778 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq1957 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq411
       have i₂ := eq1954
       grind)
    | exact superpose eq1954 eq411
    | exact resolve eq411 eq1954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq1954
  have eq1967 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1957
  have eq1968 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1967
       have i₂ := eq1576
       grind)
    | exact superpose eq1576 eq1967
    | exact resolve eq1967 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq1969 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1968
  have eq1972 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1969
       grind)
    | exact superpose eq1969 eq16
    | exact resolve eq16 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq2000 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1972
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1972
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1972 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2001 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq2000
  have eq2003 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq2001
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2001 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq2004 : x = (M.op x y) := by
    first
    | (have i₁ := eq2003
       have i₂ := eq1576
       grind)
    | exact superpose eq1576 eq2003
    | exact resolve eq2003 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576 eq2003
  have eq2005 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1972
       have i₂ := eq2004
       grind)
    | exact superpose eq2004 eq1972
    | exact resolve eq1972 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972 eq2004
  have eq2017 : False := by grind
  exact eq2017

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq65 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq91 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq15
    | exact resolve eq15 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq91
    | exact resolve eq91 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq91
  have eq119 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq102
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       have j1 := eq119 X0 X1
       grind)
    | (have r₁ := eq133 X0 X1
       have r₂ := eq119 X0 X1
       grind)
    | (have r₁ := eq133 X0 (σ (M.op X0 X0))
       have r₂ := eq119 X0 X1
       grind)
    | (have r₁ := eq133 (M.op X0 X0) (σ X0)
       have r₂ := eq119 X0 X1
       grind)
    | exact resolve eq133 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq133
  have eq164 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq142
    | exact resolve eq142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq142 X1 (σ X0)
       grind)
    | exact superpose eq142 eq15
    | (have j1 := eq142 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq176 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq164 (τ X1) X0
       grind)
    | exact superpose eq164 eq19
    | (have j1 := eq164 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq164
  have eq260 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq176
    | exact resolve eq176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq283 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq260 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq260
    | (have j0 := eq260 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq835 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 x y
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq847 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq835
       have i₂ := eq283 y x
       grind)
    | exact superpose eq283 eq835
    | (have j1 := eq283 (σ x) (σ y)
       grind)
    | (have r₁ := eq835
       have r₂ := eq283 y x
       grind)
    | (have r₁ := eq835
       have r₂ := eq283 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq835
       have r₂ := eq283 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq835 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq835
  have eq848 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq847
  have eq850 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq848
       grind)
    | exact superpose eq848 eq16
    | exact resolve eq16 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq851 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq850
       have r₂ := eq102 x
       grind)
    | exact resolve eq850 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq852 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq851
       grind)
    | exact superpose eq851 eq16
    | exact resolve eq16 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq851
       grind)
    | exact superpose eq851 eq10
    | exact resolve eq10 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq894 : x = y := by
    first
    | (have i₁ := eq853
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq853
    | exact resolve eq853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq895 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq852
       have i₂ := eq102 x
       grind)
    | exact superpose eq102 eq852
    | exact resolve eq852 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq852
  have eq896 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq895
       have i₂ := eq894
       grind)
    | exact superpose eq894 eq895
    | exact resolve eq895 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq895
  have eq897 : False := by grind
  exact eq897
