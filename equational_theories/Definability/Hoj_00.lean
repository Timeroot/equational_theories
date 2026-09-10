import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pxy_Equation1443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X1) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq20
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq23
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq68 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq32
    | exact resolve eq32 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq131 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq68
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq154 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    grind
  have eq156 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (k X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq159 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    grind
  have eq234 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq131 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq131
    | exact resolve eq131 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq513 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq234 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq234
    | exact resolve eq234 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq842 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq513 X1 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq513
    | exact resolve eq513 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq1221 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq19 x y
       grind)
    | exact superpose eq19 eq9
    | (have j1 := eq19 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq19 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq19 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1223 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (k X0 X1))) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq16
    | (have j1 := eq19 X0 X1
       grind)
    | exact resolve eq16 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 (M.op X0 X2))) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq16
    | (have j1 := eq19 X0 X1
       grind)
    | exact resolve eq16 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1230 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq1221
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1221
    | exact resolve eq1221 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1306 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq19 (σ x) (σ y)
       grind)
    | exact superpose eq19 eq1230
    | (have j1 := eq19 x y
       grind)
    | (have r₁ := eq1230
       have r₂ := eq19 (σ x) (σ y)
       grind)
    | (have r₁ := eq1230
       have r₂ := eq19 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1230
       have r₂ := eq19 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1230 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1307 : x = y ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq1306
  have eq1383 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1307
       grind)
    | exact superpose eq1307 eq9
    | exact resolve eq9 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq1384 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq1383
  have eq1385 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1384
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1384
    | exact resolve eq1384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq1386 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq1385
  have eq1387 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq1386
  have eq1469 : (k y y) ≠ (k y y) ∨ x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq1387
       grind)
    | exact superpose eq1387 eq18
    | (have j0 := eq18 x y
       grind)
    | (have r₁ := eq18 x y
       have r₂ := eq1387
       grind)
    | (have r₁ := eq18 (σ x) (σ y)
       have r₂ := eq1387
       grind)
    | exact resolve eq18 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1472 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq1469
  have eq1555 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq1472
       grind)
    | exact superpose eq1472 eq10
    | exact resolve eq10 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq2321 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    grind
  have eq2470 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq18 (σ x) (σ y)
       have i₂ := eq1555
       grind)
    | exact superpose eq1555 eq18
    | (have j0 := eq18 (σ x) (σ y)
       grind)
    | (have r₁ := eq18 (σ x) (σ y)
       have r₂ := eq1555
       grind)
    | exact resolve eq18 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1555
  have eq2473 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq2470
  have eq2474 : x = y ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2473
  have eq2477 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq2474
       grind)
    | exact superpose eq2474 eq9
    | exact resolve eq9 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq2478 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2477
  have eq2479 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2478
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2478
    | exact resolve eq2478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq2480 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2479
  have eq2481 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2480
  have eq2509 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq842 x (σ y)
       have i₂ := eq2481
       grind)
    | exact superpose eq2481 eq842
    | exact resolve eq842 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq2542 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2509
       have i₂ := eq15 y
       grind)
    | exact superpose eq15 eq2509
    | exact resolve eq2509 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509
  have eq15421 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1223 (σ x) (σ y) X0
       have i₂ := eq2481
       grind)
    | exact superpose eq2481 eq1223
    | (have j0 := eq1223 (σ x) (σ y) x
       grind)
    | exact resolve eq1223 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15484 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1223 x y X0
       have i₂ := eq2542
       grind)
    | exact superpose eq2542 eq1223
    | (have j0 := eq1223 x y x
       grind)
    | exact resolve eq1223 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq15503 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15421
  have eq15507 : ∀ X0 : G, x = (M.op (M.op x X0) (k x y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq19 eq15484
    | (have j1 := eq19 x y
       grind)
    | exact resolve eq15484 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15484
  have eq15570 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq19 eq15503
    | (have j1 := eq19 (σ x) (σ y)
       grind)
    | exact resolve eq15503 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15503
  have eq15576 : ∀ X0 : G, (M.op x y) = (k y y) ∨ x = y ∨ x = (M.op (M.op x X0) y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2542 eq15507
    | exact resolve eq15507 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15507
  have eq15585 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq2481 eq15570
    | exact resolve eq15570 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15570
  have eq15595 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (σ (k y y)) ∨ x = y ∨ x = (M.op (M.op x X0) y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9
       have i₂ := eq15576 X0
       grind)
    | exact superpose eq15576 eq9
    | (have j1 := eq15576 X0
       grind)
    | exact resolve eq9 eq15576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15576
  have eq15621 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op (M.op x X0) y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq15595 X0
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq15595
    | (have j0 := eq15595 X0
       grind)
    | exact resolve eq15595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15595
  have eq18451 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (σ x) X0))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1224 (σ x) (σ y) X0
       have i₂ := eq2481
       grind)
    | exact superpose eq2481 eq1224
    | (have j0 := eq1224 (σ x) (σ y) x
       grind)
    | exact resolve eq1224 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481
  have eq18522 : ∀ X0 : G, (M.op x y) = (k y y) ∨ x = y ∨ x = (M.op y (M.op x (M.op x X0))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1224 x y X0
       have i₂ := eq2542
       grind)
    | exact superpose eq2542 eq1224
    | (have j0 := eq1224 x y x
       grind)
    | exact resolve eq1224 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq2542
  have eq18622 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (σ x) X0))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18451
  have eq18671 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (σ (k y y)) ∨ x = y ∨ x = (M.op y (M.op x (M.op x X0))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9
       have i₂ := eq18522 X0
       grind)
    | exact superpose eq18522 eq9
    | (have j1 := eq18522 X0
       grind)
    | exact resolve eq9 eq18522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18522
  have eq18704 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op y (M.op x (M.op x X0))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18671 X0
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq18671
    | (have j0 := eq18671 X0
       grind)
    | exact resolve eq18671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18671
  have eq28436 : ∀ X1 : G, (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X1))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq16 (σ y) (M.op (σ x) (M.op (σ x) x)) X1
       have i₂ := eq18622 x
       grind)
    | exact superpose eq18622 eq16
    | exact resolve eq16 eq18622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18622
  have eq29209 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq15585 (M.op (σ y) (M.op (σ y) x))
       have i₂ := eq28436 x
       grind)
    | exact superpose eq28436 eq15585
    | exact resolve eq15585 eq28436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15585 eq28436
  have eq29227 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq29209
  have eq29246 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq29227
  have eq29616 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op (M.op x X0) y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15621 X0
       have i₂ := eq29246
       grind)
    | exact superpose eq29246 eq15621
    | (have j0 := eq15621 X0
       grind)
    | (have r₁ := eq15621 X0
       have r₂ := eq29246
       grind)
    | exact resolve eq15621 eq29246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15621
  have eq29617 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op y (M.op x (M.op x X0))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18704 X0
       have i₂ := eq29246
       grind)
    | exact superpose eq29246 eq18704
    | (have j0 := eq18704 X0
       grind)
    | (have r₁ := eq18704 X0
       have r₂ := eq29246
       grind)
    | exact resolve eq18704 eq29246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18704 eq29246
  have eq29651 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op y (M.op x (M.op x X0))) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29617
  have eq29652 : ∀ X0 : G, x = (M.op y (M.op x (M.op x X0))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29651
  have eq29653 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op (M.op x X0) y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29616 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29616
  have eq29654 : ∀ X0 : G, x = (M.op (M.op x X0) y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29653 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29653
  have eq30822 : ∀ X1 : G, y = (M.op x (M.op y (M.op y X1))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq16 y (M.op x (M.op x x)) X1
       have i₂ := eq29652 x
       grind)
    | exact superpose eq29652 eq16
    | exact resolve eq16 eq29652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29652
  have eq31629 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq29654 (M.op y (M.op y x))
       have i₂ := eq30822 x
       grind)
    | exact superpose eq30822 eq29654
    | exact resolve eq29654 eq30822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29654 eq30822
  have eq31645 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq31629
  have eq31669 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq31645
  have eq32360 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq31669
       grind)
    | exact superpose eq31669 eq10
    | exact resolve eq10 eq31669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31669
  have eq32361 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq32360
  have eq32487 : (k y y) = (τ (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20 y y
       have i₂ := eq32361
       grind)
    | exact superpose eq32361 eq20
    | exact resolve eq20 eq32361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq32591 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq156 (σ y) X0
       have i₂ := eq32361
       grind)
    | exact superpose eq32361 eq156
    | exact resolve eq156 eq32361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32592 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ y) X0))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq154 (σ y) X0
       have i₂ := eq32361
       grind)
    | exact superpose eq32361 eq154
    | exact resolve eq154 eq32361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq32723 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32487
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq32487
    | exact resolve eq32487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32487
  have eq32917 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq156 y X0
       have i₂ := eq32723
       grind)
    | exact superpose eq32723 eq156
    | exact resolve eq156 eq32723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq33067 : y = (M.op (k y y) (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq33075 : y = (k (M.op y x) (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq32917
  have eq33101 : y = (M.op x (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32723 eq33067
    | exact resolve eq33067 eq32723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33067
  have eq33130 : ∀ X0 : G, x = (M.op y (M.op x (M.op x X0))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x (M.op y x) X0
       have i₂ := eq33101
       grind)
    | exact superpose eq33101 eq16
    | exact resolve eq16 eq33101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33138 : x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq159 x (M.op y x)
       have i₂ := eq33101
       grind)
    | exact superpose eq33101 eq159
    | exact resolve eq159 eq33101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq33194 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2321 (σ y)
       have i₂ := eq32361
       grind)
    | exact superpose eq32361 eq2321
    | exact resolve eq2321 eq32361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq33395 : (σ y) = (k (σ (M.op y x)) (σ (M.op y x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op y x) (M.op y x)
       have i₂ := eq33075
       grind)
    | exact superpose eq33075 eq10
    | exact resolve eq10 eq33075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33075
  have eq33416 : x = (M.op y (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33130 (M.op y x)
       have i₂ := eq33101
       grind)
    | exact superpose eq33101 eq33130
    | exact resolve eq33130 eq33101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33101 eq33130
  have eq33451 : x = (M.op y (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq33416
  have eq33504 : x = (M.op y (k y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq33451
       have i₂ := eq1387
       grind)
    | exact superpose eq1387 eq33451
    | exact resolve eq33451 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33451
  have eq33537 : x = (M.op y (k y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq33504
  have eq33544 : x = (M.op y (k y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32361 eq33537
    | exact resolve eq33537 eq32361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33537
  have eq33548 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32723 eq33544
    | exact resolve eq33544 eq32723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32723 eq33544
  have eq33792 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op x y) (M.op x y)
       have i₂ := eq33138
       grind)
    | exact superpose eq33138 eq10
    | exact resolve eq10 eq33138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33138
  have eq34130 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (σ x) X0))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 (σ x) (M.op (σ y) (σ x)) X0
       have i₂ := eq33194
       grind)
    | exact superpose eq33194 eq16
    | exact resolve eq16 eq33194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34131 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 (σ x) X0 (M.op (σ y) (σ x))
       have i₂ := eq33194
       grind)
    | exact superpose eq33194 eq16
    | exact resolve eq16 eq33194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33194
  have eq36160 : (σ x) = (k (σ (k y y)) (σ (k y y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq33792
       have i₂ := eq1387
       grind)
    | exact superpose eq1387 eq33792
    | exact resolve eq33792 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387 eq33792
  have eq36277 : (σ x) = (k (σ (k y y)) (σ (k y y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq36160
  have eq36388 : (σ x) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36277
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq36277
    | exact resolve eq36277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36277
  have eq36498 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq32361 eq36388
    | exact resolve eq36388 eq32361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36388
  have eq36502 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32361 eq36498
    | exact resolve eq36498 eq32361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32361 eq36498
  have eq41144 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34130 (M.op (σ y) (M.op (σ y) x))
       have i₂ := eq32592 x
       grind)
    | exact superpose eq32592 eq34130
    | exact resolve eq34130 eq32592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32592 eq34130
  have eq41173 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq41144
  have eq42392 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33395
       have i₂ := eq33548
       grind)
    | exact superpose eq33548 eq33395
    | exact resolve eq33395 eq33548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33395 eq33548
  have eq42425 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq42392
  have eq42442 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36502 eq42425
    | exact resolve eq42425 eq36502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36502 eq42425
  have eq42443 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq42442
  have eq42485 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41173
       have i₂ := eq42443
       grind)
    | exact superpose eq42443 eq41173
    | exact resolve eq41173 eq42443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41173
  have eq42497 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34131 (σ y)
       have i₂ := eq42443
       grind)
    | exact superpose eq42443 eq34131
    | exact resolve eq34131 eq42443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34131 eq42443
  have eq42514 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq42497
  have eq42526 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq42485
  have eq42559 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq42514
  have eq42644 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32591 (σ x)
       have i₂ := eq42526
       grind)
    | exact superpose eq42526 eq32591
    | exact resolve eq32591 eq42526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32591 eq42526
  have eq42665 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq42644
  have eq42673 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq42665
  have eq42676 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq42559 eq42673
    | exact resolve eq42673 eq42559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42559 eq42673
  have eq42677 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq42676
  have eq42680 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq42677
       grind)
    | exact superpose eq42677 eq9
    | exact resolve eq9 eq42677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42677
  have eq42681 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq42680
  have eq42682 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42681
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq42681
    | exact resolve eq42681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42681
  have eq42683 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq42682
  have eq42684 : (σ x) = (σ y) := by grind
  clear eq42683
  have eq42686 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq42684
       grind)
    | exact superpose eq42684 eq15
    | exact resolve eq15 eq42684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42684
  have eq42927 : x = y := by
    first
    | (have i₁ := eq42686
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq42686
    | exact resolve eq42686 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42686
  have eq43426 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq42927
       grind)
    | exact superpose eq42927 eq9
    | exact resolve eq9 eq42927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42927
  have eq43427 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq43426
  have eq43428 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43427
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq43427
    | exact resolve eq43427 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43427
  have eq43429 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq43428
  have eq43430 : False := by grind
  exact eq43430

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
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
  clear eq18
  have eq195 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq208 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq195
    | (have j0 := eq195 X0
       grind)
    | exact resolve eq195 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq195
  have eq210 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq208 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq208
    | (have j0 := eq208 X0
       grind)
    | exact resolve eq208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq211 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq210 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq210 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq210 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq218 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq211 (σ X0)
       grind)
    | exact superpose eq211 eq15
    | exact resolve eq15 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq218
    | exact resolve eq218 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq360 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq16
    | (have j1 := eq88 x y
       grind)
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1276 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq1320 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1276 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1276
    | (have j0 := eq1276 X0 X1
       grind)
    | exact resolve eq1276 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1937 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq360
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq360
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq360
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq360
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq360 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1938 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq1937
  have eq48199 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1938
       grind)
    | exact superpose eq1938 eq16
    | exact resolve eq16 eq1938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq48200 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq48199
       have r₂ := eq225 x
       grind)
    | exact resolve eq48199 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48199
  have eq62904 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq48200
       grind)
    | exact superpose eq48200 eq10
    | exact resolve eq10 eq48200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48200
  have eq63007 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62904
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq62904
    | exact resolve eq62904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62904
  have eq63023 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63007
       grind)
    | exact superpose eq63007 eq16
    | exact resolve eq16 eq63007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63007
  have eq63024 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq63023
       have r₂ := eq225 x
       grind)
    | exact resolve eq63023 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63023
  have eq64449 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq63024
       grind)
    | exact superpose eq63024 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq63024
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq63024
       grind)
    | exact resolve eq12 eq63024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63024
  have eq64554 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq64449
  have eq65440 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq360
       have i₂ := eq64554
       grind)
    | exact superpose eq64554 eq360
    | exact resolve eq360 eq64554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq64554
  have eq65453 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq65440
  have eq65454 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq65453
  have eq65457 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq65454
       grind)
    | exact superpose eq65454 eq10
    | exact resolve eq10 eq65454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65454
  have eq65560 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq65457
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq65457
    | exact resolve eq65457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65457
  have eq66543 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65560
       grind)
    | exact superpose eq65560 eq16
    | exact resolve eq16 eq65560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65560
  have eq66549 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq66543
       have r₂ := eq225 x
       grind)
    | exact resolve eq66543 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq66543
  have eq66583 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq66549
       grind)
    | exact superpose eq66549 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq66549
       grind)
    | exact resolve eq12 eq66549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66549
  have eq66690 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq66583
  have eq66757 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq66690
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq66690
    | exact resolve eq66690 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66690
  have eq67851 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66757
       grind)
    | exact superpose eq66757 eq16
    | exact resolve eq16 eq66757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66757
  have eq68563 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq67851
       have i₂ := eq1320 x y
       grind)
    | exact superpose eq1320 eq67851
    | (have j1 := eq1320 x y
       grind)
    | (have r₁ := eq67851
       have r₂ := eq1320 x y
       grind)
    | (have r₁ := eq67851
       have r₂ := eq1320 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq67851
       have r₂ := eq1320 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq67851 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq68564 : x = y ∨ y = (M.op y x) := by grind
  clear eq68563
  have eq68574 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq67851
       have i₂ := eq68564
       grind)
    | exact superpose eq68564 eq67851
    | exact resolve eq67851 eq68564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68564
  have eq68575 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq68574
       have i₂ := eq211 x
       grind)
    | exact superpose eq211 eq68574
    | exact resolve eq68574 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq68574
  have eq68576 : y = (M.op y x) := by grind
  clear eq68575
  have eq69376 : y ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq68576
       grind)
    | exact superpose eq68576 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq68576
       grind)
    | exact resolve eq12 eq68576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68576
  have eq69484 : (M.op x y) = (k x y) := by grind
  clear eq69376
  have eq70250 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq67851
       have i₂ := eq69484
       grind)
    | exact superpose eq69484 eq67851
    | exact resolve eq67851 eq69484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67851 eq69484
  have eq70259 : False := by grind
  exact eq70259

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq43 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq52 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq52
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq60
  have eq130 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq134 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq130 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq130 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq130 X0 X0
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq130 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq130
  have eq277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq280 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 X1
       have i₂ := eq134 X0 X1
       grind)
    | exact superpose eq134 eq277
    | exact resolve eq277 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq277
  have eq283 : False := by grind
  exact eq283

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyy_pxy_Equation1469 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq19 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq21 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : (M.op x y) = (M.op x y) := by grind
  have eq25 : (M.op x y) = (M.op x y) := by grind
  clear eq24
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq27 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq26
  have eq28 : (σ x) = (σ x) := by grind
  have eq29 : (σ x) = (σ x) := by grind
  clear eq28
  have eq30 : (σ y) = (σ y) := by grind
  have eq31 : (σ y) = (σ y) := by grind
  clear eq30
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq33 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq32
  have eq34 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq19
    | (have j1 := eq20 X0
       grind)
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq36 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq23 eq22
    | (have j1 := eq23 X0
       grind)
    | exact resolve eq22 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq35
  have eq42 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq25
    | exact resolve eq25 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq39
  have eq43 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq41
       grind)
    | exact superpose eq41 eq42
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq48 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq49 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op x y) (M.op X0 (M.op X0 (τ (σ x))))) := by
    intro X0
    first
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq33 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (k X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq55 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op (τ (σ y)) X0) (M.op (τ (σ x)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq33 eq9
    | (have j0 := eq9 (σ y) X0 (σ x)
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    grind
  have eq61 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    grind
  clear eq60
  have eq107 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq43 eq14
    | (have j0 := eq14 (M.op x y) (k (τ (σ x)) (τ (σ y)))
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X1 : G, (M.op x y) = (M.op (τ (σ x)) (M.op X1 (M.op X1 (M.op x y)))) := by
    intro X1
    first
    | exact superpose eq50 eq9
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    grind
  have eq302 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq358 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq49 X0 X1 X2
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op X0 (M.op (τ (σ x)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq246 eq49
    | exact resolve eq49 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq390 : ∀ X0 : G, (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op X0 (M.op (τ (σ x)) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq365 eq48
    | exact resolve eq48 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq365
  have eq439 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (τ (σ y))) := by
    first
    | exact superpose eq55 eq390
    | exact resolve eq390 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq390
  have eq457 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op (τ (σ y)) X0) (M.op (k (M.op x y) (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq439 eq9
    | exact resolve eq9 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq465 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq109 eq34
    | exact resolve eq34 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq2577 : (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq302 eq49
    | exact resolve eq49 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq2805 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op X0 (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0 (k X0 X0) (k X0 X0)
       have i₂ := eq248 X0
       grind)
    | exact superpose eq248 eq49
    | exact resolve eq49 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq5467 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (τ (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq50 sF2
       have i₂ := eq358 sF2 (τ sF4) sF2
       grind)
    | (have i₁ := eq50 X0
       have i₂ := eq358 X0 (τ sF4) sF2
       grind)
    | exact superpose eq358 eq50
    | exact resolve eq50 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq358
  have eq97307 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq97347 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq97307
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq97307
    | exact resolve eq97307 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97307
  have eq97348 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq97347
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq97347
    | exact resolve eq97347 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97347
  have eq97349 : (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq27 eq97348
    | exact resolve eq97348 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97348
  have eq98782 : (τ (σ y)) = (M.op (M.op x y) (M.op (k (M.op x y) (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq97349 eq457
    | exact resolve eq457 eq97349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq98791 : (τ (σ x)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq97349 eq5467
    | exact resolve eq5467 eq97349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5467 eq97349
  have eq98931 : (τ (σ x)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq98791
  have eq98934 : (τ (σ y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq98782
       have i₂ := eq2805 sF2
       grind)
    | exact superpose eq2805 eq98782
    | exact resolve eq98782 eq2805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805 eq98782
  have eq111191 : (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq98934 eq98931
    | exact resolve eq98931 eq98934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98931 eq98934
  have eq111335 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq111191
  have eq111400 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq111335 eq465
    | (have r₁ := eq465
       have r₂ := eq111335
       grind)
    | exact resolve eq465 eq111335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq111335
  have eq111472 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq111400
  have eq112531 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq111472 eq57
    | exact resolve eq57 eq111472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq112544 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq111472 eq52
    | exact resolve eq52 eq111472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq111472
  have eq112674 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq2577 eq112531
    | exact resolve eq112531 eq2577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577 eq112531
  have eq115005 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq112674 eq61
    | exact resolve eq61 eq112674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq112674
  have eq115218 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq115005 eq112544
    | exact resolve eq112544 eq115005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112544 eq115005
  have eq115221 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq115218
  have eq115225 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq115221
       have i₂ := eq248 sF5
       grind)
    | exact superpose eq248 eq115221
    | exact resolve eq115221 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq115221
  have eq115226 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq115225
  have eq116980 : (σ y) = (σ (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq115226 eq36
    | exact resolve eq36 eq115226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115226
  have eq116996 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq116980
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq116980
    | exact resolve eq116980 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116980
  have eq116997 : (σ x) = (σ y) := by grind
  clear eq116996
  have eq117010 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq116997 eq33
    | exact resolve eq33 eq116997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq117011 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq116997 eq43
    | exact resolve eq43 eq116997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq116997
  have eq117066 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by grind
  clear eq117011
  have eq117067 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq117010
  have eq117747 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq117067 eq34
    | exact resolve eq34 eq117067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq117067
  have eq118420 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) := by
    first
    | exact superpose eq117066 eq15
    | exact resolve eq15 eq117066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117066
  have eq118422 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq118420
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq118420
    | exact resolve eq118420 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq118420
  have eq118519 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq118422 eq27
    | exact resolve eq27 eq118422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq118422
  have eq118584 : False := by grind
  exact eq118584

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyx_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 X1 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X1 (M.op X2 X0)) X3 X4 (M.op X0 x)
       have i₂ := eq14 X0 x X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ (k x (k x y))) = (k (σ x) (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq35 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq35
    | exact resolve eq35 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq58 : ∀ X0 : G, (σ (k X0 (k x y))) = (k (σ X0) (k (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X0 ∨ (M.op X2 (M.op X0 (M.op X1 X0))) = (k X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op X1 X0))
       have i₂ := eq14 X0 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq76
    | (have j0 := eq76 (σ X0) (σ X1)
       grind)
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq76 y x
       grind)
    | exact superpose eq76 eq73
    | (have j1 := eq76 y x
       grind)
    | exact resolve eq73 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
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
  have eq109 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq119 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq130 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq139 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq149 : (σ (k (k x y) x)) = (k (k (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq39 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq39
    | exact resolve eq39 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : (σ (k (k y x) x)) = (k (k (σ y) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq39 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq39
    | exact resolve eq39 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq161 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq130
       have i₂ := eq76 sF0 sF0
       grind)
    | exact superpose eq76 eq130
    | (have j1 := eq76 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq130 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq169 : (k (M.op x y) x) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq76 sF1 sF2
       grind)
    | exact superpose eq76 eq139
    | (have j1 := eq76 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq139 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : (σ (k (k x y) (M.op x y))) = (k (k (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq41
    | exact resolve eq41 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq76 (σ X0) sF1
       grind)
    | exact superpose eq76 eq41
    | (have j1 := eq76 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq208 : ∀ X2 X3 : G, (M.op x y) = (M.op x (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X2 X3
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) ∨ (M.op x y) = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq213 eq12
    | (have j0 := eq12 X0 (M.op x y)
       grind)
    | exact resolve eq12 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq222 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq293 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq322 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq38
  have eq385 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq14 X0 x X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq406 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X2 (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 y X2 X0
       have i₂ := eq386 X0 X1
       grind)
    | (have i₁ := eq52 x y x X0
       have i₂ := eq386 X0 X1
       grind)
    | exact superpose eq386 eq52
    | exact resolve eq52 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq243
    | exact resolve eq243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq243
    | (have j0 := eq243 X0 (M.op x y)
       grind)
    | exact resolve eq243 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 : G, (k (k x y) (τ X0)) = (τ (k (k (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq322 (k x y) X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq322
    | exact resolve eq322 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq672 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X2 X4 (M.op (M.op X0 (M.op X1 X2)) x)
       have i₂ := eq55 X2 X0 X1 x X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq681 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X0 (M.op X1 X2)) X2) ∨ (M.op X3 (M.op (M.op X0 (M.op X1 X2)) X2)) = (k X3 (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op (M.op X0 (M.op X1 X2)) X2)
       have i₂ := eq55 X2 X0 X1 X2 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq55 eq13
    | (have j0 := eq13 X3 (M.op (M.op X0 (M.op X1 X2)) X2)
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq727
    | exact resolve eq727 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq731 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq728
       have r₂ := eq27
       grind)
    | exact resolve eq728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq734 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq731 eq51
    | exact resolve eq51 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq731 eq12
    | (have j0 := eq12 x (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq731
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq731
       grind)
    | exact resolve eq12 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq735
  have eq746 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq387 eq734
    | (have j0 := eq734 (σ x)
       grind)
    | exact resolve eq734 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq783 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op X2 (M.op X3 (σ X0)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (σ X0) (σ X1) X2 X3
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq14
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq14 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (M.op (σ X1) X2) (M.op X3 (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (σ X1) X2 X3 (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq14
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq14 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (M.op (σ (k X0 X1)) X2) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (σ X1) (σ X0) X2
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq56
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq56 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq810 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op (M.op X0 (σ x)) X1) (M.op X2 (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq746 eq55
    | exact resolve eq55 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq872 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 X2) ≠ (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) ∨ (M.op X5 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2)))) = (k X5 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq66 (M.op x X0) (M.op (M.op X1 (M.op X2 X0)) X3) X2
       have i₂ := eq55 X0 X1 X2 X3 x
       grind)
    | exact superpose eq55 eq66
    | exact resolve eq66 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq66
  have eq1033 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq731 eq385
    | exact resolve eq385 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq742 eq60
    | exact resolve eq60 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq742
  have eq1257 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq1253
    | exact resolve eq1253 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1287 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1257 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1257
       grind)
    | exact resolve eq13 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1299 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1287 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq3936 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq789 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq789
    | (have j0 := eq789 (τ X0)
       grind)
    | exact resolve eq789 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3937 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq789 x
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq789
    | (have j0 := eq789 x
       grind)
    | exact resolve eq789 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq3942 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3937
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3937
    | exact resolve eq3937 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937
  have eq3943 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3936 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3936
    | (have j0 := eq3936 X0
       grind)
    | exact resolve eq3936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq3947 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3942
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3942
    | exact resolve eq3942 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3942
  have eq3948 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3943 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3943
    | (have j0 := eq3943 X0
       grind)
    | exact resolve eq3943 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3943
  have eq4938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1299 eq110
    | exact resolve eq110 eq1299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq4953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (k x y) := by grind
  clear eq4938
  have eq4963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq4953
    | exact resolve eq4953 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4953
  have eq4965 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq4963
       have r₂ := eq27
       grind)
    | exact resolve eq4963 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4963
  have eq4968 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq4965
       grind)
    | exact superpose eq4965 eq44
    | exact resolve eq44 eq4965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4969 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq76 x y
       have i₂ := eq4965
       grind)
    | exact superpose eq4965 eq76
    | (have j0 := eq76 x y
       grind)
    | exact resolve eq76 eq4965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4970 : y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq4969
  have eq4972 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4970
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4970
    | exact resolve eq4970 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4970
  have eq4973 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4968
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4968
    | exact resolve eq4968 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4968
  have eq6225 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 (σ (M.op x y))))) (M.op X1 (M.op X2 (σ (τ X0))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq498 eq783
    | (have j0 := eq783 (τ X0) (M.op x y) X2 x
       grind)
    | exact resolve eq783 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq6254 : ∀ X0 X1 : G, (σ y) = (M.op (k (σ y) (σ x)) (M.op X0 (M.op X1 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq783 y x X0 X1
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq783
    | (have j0 := eq783 y x x x
       grind)
    | exact resolve eq783 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6335 : ∀ X0 X1 : G, (σ y) = (M.op (k (σ y) (σ x)) (M.op X0 (M.op X1 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq6254 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6254
    | (have j0 := eq6254 X0 X1
       grind)
    | exact resolve eq6254 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6254
  have eq6353 : ∀ X0 X1 X2 : G, (M.op (σ (τ (k X0 (σ (M.op x y))))) (M.op X1 (M.op X2 X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6225 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6225
    | (have j0 := eq6225 X0 X1 X2
       grind)
    | exact resolve eq6225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6225
  have eq6372 : ∀ X0 : G, (σ y) = (M.op (k (σ y) (σ x)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq387 eq6335
    | (have j0 := eq6335 X0 (σ x)
       grind)
    | exact resolve eq6335 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6335
  have eq6389 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ (M.op x y))) (M.op X1 (M.op X2 X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6353 X0 X1 X2
       have i₂ := eq15 (k X0 sF1)
       grind)
    | exact superpose eq15 eq6353
    | (have j0 := eq6353 X0 X1 X2
       grind)
    | exact resolve eq6353 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6353
  have eq6405 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq6372 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6372
    | (have j0 := eq6372 X0
       grind)
    | exact resolve eq6372 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6372
  have eq6420 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (M.op (k X0 (σ (M.op x y))) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6389 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6389
    | (have j0 := eq6389 X0 X1 X2
       grind)
    | exact resolve eq6389 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6389
  have eq6430 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq6405 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6405
    | (have j0 := eq6405 X0
       grind)
    | exact resolve eq6405 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6405
  have eq6434 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ (M.op x y))) (M.op X1 (M.op X2 X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq20 eq6420
    | (have j0 := eq6420 X0 X1 X2
       grind)
    | exact resolve eq6420 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6420
  have eq6443 : ∀ X0 : G, (σ y) = (M.op (k (σ y) (σ x)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq6430
    | (have j0 := eq6430 X0
       grind)
    | exact resolve eq6430 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6430
  have eq6489 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 (M.op x y))) (M.op X1 (σ (k X2 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X2)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq203 eq784
    | (have j0 := eq784 X2 X0 X2 x
       have j1 := eq203 X0
       grind)
    | exact resolve eq784 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq6562 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (k (σ x) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq45 eq784
    | (have j0 := eq784 x (M.op x y) x x
       grind)
    | exact resolve eq784 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq6619 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (k (σ x) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq6562
    | (have j0 := eq6562 X0 X1
       grind)
    | exact resolve eq6562 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6562
  have eq6658 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (k (σ x) (σ (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6619 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6619
    | (have j0 := eq6619 X0 X1
       grind)
    | exact resolve eq6619 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6619
  have eq6693 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (k (σ x) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq6658
    | (have j0 := eq6658 X0 X1
       grind)
    | exact resolve eq6658 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6658
  have eq6773 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (M.op (k (σ y) (σ x)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq788 y x x
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq788
    | (have j0 := eq788 y x x
       grind)
    | exact resolve eq788 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq6874 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (M.op (k (σ y) (σ x)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6773 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6773
    | (have j0 := eq6773 X0
       grind)
    | exact resolve eq6773 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6773
  have eq6912 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (M.op (k (σ y) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6874 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6874
    | (have j0 := eq6874 X0
       grind)
    | exact resolve eq6874 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6874
  have eq6945 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (M.op (k (σ y) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6912 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6912
    | (have j0 := eq6912 X0
       grind)
    | exact resolve eq6912 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6912
  have eq6969 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (M.op (k (σ y) (σ x)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq6945
    | (have j0 := eq6945 X0
       grind)
    | exact resolve eq6945 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6945
  have eq10951 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 X2) ≠ (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) ∨ (M.op X5 X2) = (k X5 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq872 X0 X1 X2 X3 X5
       have i₂ := eq672 X0 X1 X2 X5 (M.op X3 X2)
       grind)
    | exact superpose eq672 eq872
    | (have j0 := eq872 X0 X1 X2 X3 X5
       grind)
    | exact resolve eq872 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq872
  have eq11405 : ∀ X0 X1 X3 : G, (M.op X0 (σ y)) ≠ (M.op (M.op X0 (σ y)) (M.op X1 (M.op (σ x) (σ y)))) ∨ (M.op X3 (σ y)) = (k X3 (M.op (M.op X0 (σ y)) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X3
    first
    | exact superpose eq222 eq10951
    | (have j0 := eq10951 X1 (σ x) (σ y) X0 X3
       grind)
    | exact resolve eq10951 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq10951
  have eq13478 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X1))) (M.op X2 (M.op X3 (σ (τ X0))))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq783 (τ X0) (τ X1) X2 X3
       have i₂ := eq482 X1 X0
       grind)
    | exact superpose eq482 eq783
    | (have j0 := eq783 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq783 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq783
  have eq13495 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ (k X0 X1))) (M.op X2 (M.op X3 X0))) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13478 X0 X1 X2 X3
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13478
    | (have j0 := eq13478 X0 X1 X2 X3
       grind)
    | exact resolve eq13478 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13478
  have eq13520 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) (M.op X2 (M.op X3 X0))) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13495 X0 X1 X2 X3
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq13495
    | (have j0 := eq13495 X0 X1 X2 X3
       grind)
    | exact resolve eq13495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13495
  have eq13539 : ∀ X0 X1 X2 X3 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op (k X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13520 X0 X1 X2 X3
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13520
    | (have j0 := eq13520 X0 X1 X2 X3
       grind)
    | exact resolve eq13520 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13520
  have eq13550 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) (M.op X2 (M.op X3 X0))) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13539 X0 X0 X2 X3
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13539
    | (have j0 := eq13539 X0 X1 X2 X3
       grind)
    | exact resolve eq13539 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13539
  have eq15990 : (τ (k (σ y) (σ x))) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq16
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16030 : (k y x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81 eq15990
    | exact resolve eq15990 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15990
  have eq25707 : (σ (k x y)) = (k (σ x) (k (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq57
       have i₂ := eq4965
       grind)
    | exact superpose eq4965 eq57
    | exact resolve eq57 eq4965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq25773 : (k (σ x) (σ y)) = (k (σ x) (k (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq25707
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq25707
    | exact resolve eq25707 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25707
  have eq25801 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq25773
    | exact resolve eq25773 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25773
  have eq25818 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq25801
  have eq25821 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq25818
       have i₂ := eq76 sF2 sF1
       grind)
    | exact superpose eq76 eq25818
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq25818 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25822 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq25818 eq64
    | exact resolve eq64 eq25818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25833 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq25822
    | exact resolve eq25822 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25822
  have eq25834 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq25833
       have i₂ := eq76 x sF0
       grind)
    | exact superpose eq76 eq25833
    | (have j1 := eq76 x (M.op x y)
       grind)
    | exact resolve eq25833 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25833
  have eq30025 : (σ (k y x)) = (k (k (σ x) (σ y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq149
       have i₂ := eq4965
       grind)
    | exact superpose eq4965 eq149
    | exact resolve eq149 eq4965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq30091 : (k (σ y) (σ x)) = (k (k (σ x) (σ y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq30025
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq30025
    | exact resolve eq30025 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30025
  have eq30116 : (k (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq30091
    | exact resolve eq30091 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30091
  have eq30133 : (k (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq30116
  have eq30137 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30133 eq81
    | exact resolve eq81 eq30133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30146 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30133 eq76
    | (have j0 := eq76 (σ y) (σ x)
       grind)
    | exact resolve eq76 eq30133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30133
  have eq30156 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq30146
    | exact resolve eq30146 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30146
  have eq30157 : (k y x) = (k (M.op x y) x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq139 eq30137
    | exact resolve eq30137 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30137
  have eq30321 : (τ (M.op (σ y) (σ x))) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30156 eq139
    | exact resolve eq139 eq30156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq30156
  have eq30607 : (τ (σ y)) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq731 eq30321
    | exact resolve eq30321 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq30321
  have eq30635 : (τ (σ y)) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq30607
  have eq30641 : y = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq30635
    | exact resolve eq30635 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30635
  have eq30730 : y = (k y x) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30641 eq30157
    | exact resolve eq30157 eq30641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30157 eq30641
  have eq30745 : y = (k y x) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30730
  have eq30796 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76 y x
       have i₂ := eq30745
       grind)
    | exact superpose eq30745 eq76
    | (have j0 := eq76 x y
       grind)
    | exact resolve eq76 eq30745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30808 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30796
  have eq30818 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30808
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30808
    | exact resolve eq30808 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30808
  have eq30839 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq30818
       grind)
    | exact superpose eq30818 eq109
    | exact resolve eq109 eq30818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30818
  have eq30899 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30839
  have eq30927 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30899
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30899
    | exact resolve eq30899 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30899
  have eq31105 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30927 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq30927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30927
  have eq31119 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq31105
    | exact resolve eq31105 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31105
  have eq31120 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31119
  have eq31218 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31120 eq51
    | exact resolve eq51 eq31120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31120
  have eq31293 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq387 eq31218
    | (have j0 := eq31218 (σ x)
       grind)
    | exact resolve eq31218 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31218
  have eq31459 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31293 eq212
    | exact resolve eq212 eq31293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31293
  have eq34118 : (σ (k y (M.op x y))) = (k (k (σ x) (σ y)) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq192
       have i₂ := eq4965
       grind)
    | exact superpose eq4965 eq192
    | exact resolve eq192 eq4965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq34184 : (k (σ y) (σ (M.op x y))) = (k (k (σ x) (σ y)) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq75 eq34118
    | exact resolve eq34118 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq34118
  have eq34209 : (k (σ y) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq34184
    | exact resolve eq34184 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34184
  have eq34226 : (k (σ y) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq34209
  have eq34233 : (k y (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq34226 eq91
    | exact resolve eq91 eq34226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34226
  have eq34249 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq164 eq34233
    | exact resolve eq34233 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34233
  have eq34259 : (M.op x y) ≠ (k y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq34249 eq3948
    | (have j0 := eq3948 (M.op x y)
       grind)
    | exact resolve eq3948 eq34249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948 eq34249
  have eq36867 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (k x y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq4973 eq58
    | exact resolve eq58 eq4973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq36899 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (k x y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq40 eq36867
    | exact resolve eq36867 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq36867
  have eq38184 : ∀ X0 : G, (k X0 (k x y)) = (τ (σ (k X0 y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 (k x y))
       have i₂ := eq36899 X0
       grind)
    | exact superpose eq36899 eq16
    | exact resolve eq16 eq36899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36899
  have eq38263 : ∀ X0 : G, (k X0 y) = (k X0 (k x y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq38184 X0
       have i₂ := eq16 (k X0 y)
       grind)
    | exact superpose eq16 eq38184
    | exact resolve eq38184 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38184
  have eq38419 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq38263 X0
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq38263
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq38263 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38263
  have eq38450 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq38419 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38419
  have eq38475 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq38450 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38450
    | (have j0 := eq38450 X0
       grind)
    | exact resolve eq38450 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq38450
  have eq38516 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq38475 eq45
    | exact resolve eq45 eq38475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq38475
  have eq38612 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq38516
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq38516
    | exact resolve eq38516 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq38516
  have eq38808 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq38612 eq4973
    | exact resolve eq4973 eq38612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4973 eq38612
  have eq38842 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq38808
  have eq38857 : (τ (σ y)) = (k x (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq38842 eq64
    | exact resolve eq64 eq38842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq38883 : y = (k x (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq38857
    | exact resolve eq38857 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38857
  have eq38947 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op y x) ∨ y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq38883
       have i₂ := eq76 x sF0
       grind)
    | exact superpose eq76 eq38883
    | (have j1 := eq76 x (M.op x y)
       grind)
    | exact resolve eq38883 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq38883
  have eq45704 : ∀ X0 : G, (k y (τ X0)) = (τ (k (k (σ x) (σ y)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq579 X0
       have i₂ := eq4965
       grind)
    | exact superpose eq4965 eq579
    | exact resolve eq579 eq4965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq4965
  have eq45772 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (k (σ x) (σ y)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq45704 X0
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq45704
    | exact resolve eq45704 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq45704
  have eq49057 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq38947 eq50
    | exact resolve eq50 eq38947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38947
  have eq52286 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (σ (M.op x y)) X0)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq110 eq45772
    | exact resolve eq45772 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq45772
  have eq52395 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (σ (M.op x y)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq52286 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52286
  have eq52519 : ∀ X0 : G, (k (τ (σ y)) X0) = (τ (k (σ (M.op x y)) (σ X0))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq52395 eq243
    | exact resolve eq243 eq52395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52395
  have eq52641 : ∀ X0 : G, (k (τ (σ (M.op x y))) X0) = (k (τ (σ y)) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq52519 x
       have i₂ := eq243 sF1 x
       grind)
    | exact superpose eq243 eq52519
    | exact resolve eq52519 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq52519
  have eq52668 : ∀ X0 : G, (k y X0) = (k (τ (σ (M.op x y))) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq29 eq52641
    | exact resolve eq52641 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52641
  have eq52676 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq30 eq52668
    | exact resolve eq52668 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52668
  have eq57982 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6443 eq6969
    | exact resolve eq6969 eq6443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6443 eq6969
  have eq58116 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq57982
  have eq74927 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq38842 eq6693
    | exact resolve eq6693 eq38842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6693 eq38842
  have eq75042 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq387 eq74927
    | (have j0 := eq74927 X0 (σ x)
       grind)
    | exact resolve eq74927 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74927
  have eq339353 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq25834 eq219
    | (have r₁ := eq219 x
       have r₂ := eq25834
       grind)
    | exact resolve eq219 eq25834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq25834
  have eq339430 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x (M.op x y)) := by grind
  clear eq339353
  have eq339433 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have r₁ := eq339430
       have r₂ := eq34259
       grind)
    | exact resolve eq339430 eq34259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34259 eq339430
  have eq339454 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq339433 eq53
    | exact resolve eq53 eq339433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339433
  have eq799387 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq339454 eq208
    | exact resolve eq208 eq339454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq339454
  have eq799541 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq799387 x
       have i₂ := eq386 x x
       grind)
    | (have i₁ := eq799387 x
       have i₂ := eq386 x x
       grind)
    | exact superpose eq386 eq799387
    | (have j0 := eq799387 x
       grind)
    | exact resolve eq799387 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799387
  have eq799542 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op y x) := by grind
  clear eq799541
  have eq799624 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 (M.op x y))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq799542 eq385
    | exact resolve eq385 eq799542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq799542
  have eq915553 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq75042 eq212
    | exact resolve eq212 eq75042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75042
  have eq1046363 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq25821 eq915553
    | exact resolve eq915553 eq25821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915553
  have eq1046500 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq1046363
  have eq1048540 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1046500 eq25821
    | exact resolve eq25821 eq1046500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25821 eq1046500
  have eq1048649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq1048540
  have eq1048661 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1048649
       have r₂ := eq27
       grind)
    | exact resolve eq1048649 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048649
  have eq1048668 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1048661 eq51
    | exact resolve eq51 eq1048661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1048672 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (M.op (σ x) (σ y)))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq1048661 eq810
    | exact resolve eq810 eq1048661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq1048769 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq1048672 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048672
  have eq1061439 : ∀ X1 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (M.op X1 (σ y)) = (k X1 (σ (M.op x y))) ∨ y = (M.op y x) := by
    intro X1
    first
    | exact superpose eq1048769 eq11405
    | exact resolve eq11405 eq1048769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11405 eq1048769
  have eq1202100 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq49057 eq799624
    | exact resolve eq799624 eq49057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49057 eq799624
  have eq1202207 : y = (M.op y x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x (M.op x y)) := by grind
  clear eq1202100
  have eq1203610 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq1202207
       grind)
    | exact superpose eq1202207 eq50
    | exact resolve eq50 eq1202207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202207
  have eq1203733 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1203610 x
       have i₂ := eq386 sF0 x
       grind)
    | (have i₁ := eq1203610 x
       have i₂ := eq386 sF0 x
       grind)
    | exact superpose eq386 eq1203610
    | (have j0 := eq1203610 x
       grind)
    | exact resolve eq1203610 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203610
  have eq1203734 : y = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq1203733
  have eq1203794 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1203734 eq406
    | exact resolve eq406 eq1203734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203734
  have eq1203945 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1203794 X0 x
       have i₂ := eq386 X0 x
       grind)
    | (have i₁ := eq1203794 X0 x
       have i₂ := eq386 X0 x
       grind)
    | exact superpose eq386 eq1203794
    | (have j0 := eq1203794 X0 x
       grind)
    | exact resolve eq1203794 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203794
  have eq1208723 : x ≠ (M.op (M.op x y) y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq1203945
  have eq2646641 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1048661 eq169
    | exact resolve eq169 eq1048661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq2647311 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq2646641
    | exact resolve eq2646641 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646641
  have eq2647366 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2647311 eq1048668
    | exact resolve eq1048668 eq2647311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048668 eq2647311
  have eq2647469 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq2647366
  have eq2647506 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq2647469 eq1033
    | exact resolve eq1033 eq2647469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq2647469
  have eq2647624 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq2647506 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647506
  have eq2678969 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq2647624 eq1061439
    | (have j0 := eq1061439 X0
       grind)
    | exact resolve eq1061439 eq2647624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061439 eq2647624
  have eq2679076 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq2678969 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678969
  have eq2679115 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq2679076 X0
       grind)
    | (have r₁ := eq2679076 X0
       have r₂ := eq1048661
       grind)
    | exact resolve eq2679076 eq1048661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048661 eq2679076
  have eq2690935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq2679115 eq25818
    | exact resolve eq25818 eq2679115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25818 eq2679115
  have eq2692442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq2690935
  have eq2693119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq2692442
    | exact resolve eq2692442 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692442
  have eq2693224 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq2693119
       have r₂ := eq27
       grind)
    | exact resolve eq2693119 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2693119
  have eq2693383 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2693224 eq52676
    | exact resolve eq52676 eq2693224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52676
  have eq2693525 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by grind
  clear eq2693383
  have eq2694153 : (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2693525
       have i₂ := eq16030
       grind)
    | exact superpose eq16030 eq2693525
    | exact resolve eq2693525 eq16030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16030 eq2693525
  have eq2699996 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq2694153
  have eq2700135 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2699996
       have r₂ := eq4972
       grind)
    | exact resolve eq2699996 eq4972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4972 eq2699996
  have eq2700194 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq2700135
       grind)
    | exact superpose eq2700135 eq109
    | exact resolve eq109 eq2700135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq2700269 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq2700135
       grind)
    | exact superpose eq2700135 eq50
    | exact resolve eq50 eq2700135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700135
  have eq2700448 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2700194
  have eq2700499 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2700269 x
       have i₂ := eq386 sF0 x
       grind)
    | (have i₁ := eq2700269 x
       have i₂ := eq386 sF0 x
       grind)
    | exact superpose eq386 eq2700269
    | (have j0 := eq2700269 x
       grind)
    | exact resolve eq2700269 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700269
  have eq2700504 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2700448
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2700448
    | exact resolve eq2700448 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700448
  have eq2700567 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2700499 eq161
    | exact resolve eq161 eq2700499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq2700750 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2700567
  have eq2700778 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2700750
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2700750
    | exact resolve eq2700750 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700750
  have eq2700829 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2700504 eq81
    | exact resolve eq81 eq2700504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq2701167 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2700829
    | exact resolve eq2700829 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2700829
  have eq2701182 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2700778 eq164
    | exact resolve eq164 eq2700778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2701384 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq2701182
    | exact resolve eq2701182 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2701182
  have eq2701398 : (σ (k y x)) = (k (k (σ y) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq151
       have i₂ := eq2701167
       grind)
    | exact superpose eq2701167 eq151
    | exact resolve eq151 eq2701167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq2701167
  have eq2701848 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2701398
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq2701398
    | exact resolve eq2701398 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2701398
  have eq2702684 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2701384 eq6489
    | (have j0 := eq6489 (M.op x y) x (M.op x y)
       grind)
    | exact resolve eq6489 eq2701384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6489
  have eq2702848 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2702684 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2702684
    | (have j0 := eq2702684 X0
       grind)
    | exact resolve eq2702684 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702684
  have eq2703012 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq2702848
    | (have j0 := eq2702848 X0
       grind)
    | exact resolve eq2702848 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702848
  have eq2703161 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq2703012
    | (have j0 := eq2703012 X0
       grind)
    | exact resolve eq2703012 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703012
  have eq2703279 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq2703161
    | (have j0 := eq2703161 X0
       grind)
    | exact resolve eq2703161 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703161
  have eq2703280 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2703279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703279
  have eq2977219 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op X1 (M.op x y)))) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq2693224 eq13550
    | (have j0 := eq13550 (M.op X0 (M.op X1 (M.op x y))) (M.op x y) x x
       grind)
    | exact resolve eq13550 eq2693224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13550 eq2693224
  have eq2980730 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq406 eq2977219
    | exact resolve eq2977219 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq2977219
  have eq3030162 : x ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2980730 eq1208723
    | exact resolve eq1208723 eq2980730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208723 eq2980730
  have eq3030337 : y = (M.op y x) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq3030162
       have r₂ := eq2700499
       grind)
    | exact resolve eq3030162 eq2700499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700499 eq3030162
  have eq3037428 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq3030337
       grind)
    | exact superpose eq3030337 eq50
    | exact resolve eq50 eq3030337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq3030337
  have eq3037593 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3037428 x
       have i₂ := eq386 sF0 x
       grind)
    | (have i₁ := eq3037428 x
       have i₂ := eq386 sF0 x
       grind)
    | exact superpose eq386 eq3037428
    | (have j0 := eq3037428 x
       grind)
    | exact resolve eq3037428 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq3037428
  have eq3037594 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x (M.op x y)) := by grind
  clear eq3037593
  have eq3037745 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3037594 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | exact resolve eq13 eq3037594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3151254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2703280 eq31459
    | exact resolve eq31459 eq2703280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31459
  have eq3151452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3151254
  have eq3151504 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3151452
       have r₂ := eq27
       grind)
    | exact resolve eq3151452 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151452
  have eq3151598 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3151504 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq3151504
       grind)
    | exact resolve eq13 eq3151504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3151669 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3151598 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151598
  have eq3156033 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3151669 eq164
    | exact resolve eq164 eq3151669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq3151669
  have eq3173464 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3151504 eq3156033
    | exact resolve eq3156033 eq3151504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151504 eq3156033
  have eq3174156 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3173464
  have eq3174167 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq3174156
    | exact resolve eq3174156 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3174156
  have eq3175394 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3174167 eq2701384
    | exact resolve eq2701384 eq3174167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701384 eq3174167
  have eq3175665 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3175394
  have eq3176130 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3175665 eq27
    | exact resolve eq27 eq3175665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3176133 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3175665 eq119
    | (have r₁ := eq119
       have r₂ := eq3175665
       grind)
    | exact resolve eq119 eq3175665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq3175665
  have eq3176310 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3176133
  have eq3197121 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3176310 eq2701848
    | exact resolve eq2701848 eq3176310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701848 eq3176310
  have eq3197320 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3197121
  have eq3197477 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3197320
       have r₂ := eq3947
       grind)
    | exact resolve eq3197320 eq3947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3947 eq3197320
  have eq3197583 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3197477 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq3197477
       grind)
    | exact resolve eq13 eq3197477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197477
  have eq3197652 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3197583 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197583
  have eq3202121 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3197652 eq2700504
    | exact resolve eq2700504 eq3197652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700504 eq3197652
  have eq3203251 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3202121
  have eq3204859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3203251 eq2703280
    | exact resolve eq2703280 eq3203251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703280 eq3203251
  have eq3204955 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq3204859
  have eq3205042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3204955
    | exact resolve eq3204955 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3204955
  have eq3205061 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3205042
       have r₂ := eq27
       grind)
    | exact resolve eq3205042 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205042
  have eq3206775 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3205061 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq3205061
       grind)
    | exact resolve eq13 eq3205061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3206846 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3206775 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3206775
  have eq3245660 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3206846 eq2700778
    | exact resolve eq2700778 eq3206846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700778 eq3206846
  have eq3247061 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq3245660
  have eq3247425 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3247061 eq3205061
    | exact resolve eq3205061 eq3247061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205061 eq3247061
  have eq3247568 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3247425
  have eq3247595 : x = (M.op x y) := by
    first
    | (have r₁ := eq3247568
       have r₂ := eq3176130
       grind)
    | exact resolve eq3247568 eq3176130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176130 eq3247568
  have eq3247600 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3247595 eq20
    | exact resolve eq20 eq3247595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3248743 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3247595 eq3037594
    | exact resolve eq3037594 eq3247595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3037594
  have eq3248744 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3247595 eq3037745
    | (have r₁ := eq3037745 X0
       have r₂ := eq3247595
       grind)
    | exact resolve eq3037745 eq3247595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3037745
  have eq3248758 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq3248744 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3248744
  have eq3248759 : x = (M.op x x) := by grind
  clear eq3248743
  have eq3248793 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3248758 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq3248758 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq3248758 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3248758
  have eq3249079 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3247600
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3247600
    | exact resolve eq3247600 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3247600
  have eq3249089 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3249079 eq26
    | exact resolve eq26 eq3249079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3249618 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3249079 eq58116
    | exact resolve eq58116 eq3249079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58116
  have eq3251027 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3249618
       have r₂ := eq27
       grind)
    | exact resolve eq3249618 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249618
  have eq3253264 : y = (M.op y x) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30745
       have i₂ := eq3248793 y
       grind)
    | exact superpose eq3248793 eq30745
    | exact resolve eq30745 eq3248793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30745
  have eq3253549 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq789 x
       have i₂ := eq3248793 x
       grind)
    | exact superpose eq3248793 eq789
    | (have j0 := eq789 x
       grind)
    | exact resolve eq789 eq3248793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3254519 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3253264
  have eq3255272 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3253549
       have i₂ := eq3248759
       grind)
    | exact superpose eq3248759 eq3253549
    | exact resolve eq3253549 eq3248759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3248759 eq3253549
  have eq3255273 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3255272
  have eq3255431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3249079 eq3254519
    | exact resolve eq3254519 eq3249079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254519
  have eq3256504 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3255273
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3255273
    | exact resolve eq3255273 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3255273
  have eq3256636 : y = (M.op y x) := by
    first
    | (have r₁ := eq3255431
       have r₂ := eq27
       grind)
    | exact resolve eq3255431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3255431
  have eq3257406 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3249079 eq3256504
    | exact resolve eq3256504 eq3249079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256504
  have eq3259271 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq3256636
       grind)
    | exact superpose eq3256636 eq53
    | exact resolve eq53 eq3256636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3259342 : ∀ X0 : G, y = (M.op (M.op y X0) x) := by
    intro X0
    first
    | (have i₁ := eq56 x y x
       have i₂ := eq3256636
       grind)
    | exact superpose eq3256636 eq56
    | exact resolve eq56 eq3256636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq3259493 : ∀ X0 : G, y = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq3247595 eq3259271
    | exact resolve eq3259271 eq3247595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259271
  have eq3260509 : (k y (M.op x y)) = (τ (M.op (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq3251027 eq91
    | exact resolve eq91 eq3251027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq3260761 : (k y x) = (τ (M.op (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq3247595 eq3260509
    | exact resolve eq3260509 eq3247595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3247595 eq3260509
  have eq3260790 : (M.op y x) = (τ (M.op (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq3260761
       have i₂ := eq3248793 y
       grind)
    | exact superpose eq3248793 eq3260761
    | exact resolve eq3260761 eq3248793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3248793 eq3260761
  have eq3260812 : y = (τ (M.op (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq3260790
       have i₂ := eq3256636
       grind)
    | exact superpose eq3256636 eq3260790
    | exact resolve eq3260790 eq3256636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260790
  have eq3260830 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq3260812 eq15
    | exact resolve eq15 eq3260812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260812
  have eq3261814 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3260830
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3260830
    | exact resolve eq3260830 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260830
  have eq3262264 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq3261814 eq14
    | exact resolve eq14 eq3261814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3262406 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq387 eq3262264
    | (have j0 := eq3262264 X0 (σ x)
       grind)
    | exact resolve eq3262264 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3262264
  have eq3270614 : y = (M.op y y) := by
    first
    | (have i₁ := eq3259493 (M.op y x)
       have i₂ := eq3259342 x
       grind)
    | exact superpose eq3259342 eq3259493
    | exact resolve eq3259493 eq3259342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259342
  have eq3270739 : ∀ X1 : G, y ≠ (M.op y x) ∨ (M.op X1 (M.op y x)) = (k X1 (M.op y x)) := by
    intro X1
    first
    | (have i₁ := eq681 y x x x
       have i₂ := eq3259493 x
       grind)
    | exact superpose eq3259493 eq681
    | exact resolve eq681 eq3259493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq3259493
  have eq3270944 : ∀ X1 : G, (M.op X1 (M.op y x)) = (k X1 (M.op y x)) := by
    intro X1
    first
    | (have j0 := eq3270739 X1
       grind)
    | (have r₁ := eq3270739 X1
       have r₂ := eq3256636
       grind)
    | exact resolve eq3270739 eq3256636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3270739
  have eq3271071 : ∀ X1 : G, (M.op X1 y) = (k X1 y) := by
    intro X1
    first
    | (have i₁ := eq3270944 X1
       have i₂ := eq3256636
       grind)
    | exact superpose eq3256636 eq3270944
    | exact resolve eq3270944 eq3256636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256636 eq3270944
  have eq3275118 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq789 y
       have i₂ := eq3271071 y
       grind)
    | exact superpose eq3271071 eq789
    | (have j0 := eq789 y
       grind)
    | exact resolve eq789 eq3271071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq3271071
  have eq3276762 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3275118
       have i₂ := eq3270614
       grind)
    | exact superpose eq3270614 eq3275118
    | exact resolve eq3275118 eq3270614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3270614 eq3275118
  have eq3276763 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3276762
  have eq3277549 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3276763
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3276763
    | exact resolve eq3276763 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3276763
  have eq3279786 : ∀ X0 : G, (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq3277549 eq6434
    | (have j0 := eq6434 (σ y) x x
       grind)
    | exact resolve eq6434 eq3277549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6434 eq3277549
  have eq3279867 : (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq387 eq3279786
    | (have j0 := eq3279786 (σ x)
       grind)
    | exact resolve eq3279786 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279786
  have eq3279926 : (σ y) = (M.op (M.op (σ y) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3251027 eq3279867
    | exact resolve eq3279867 eq3251027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3251027 eq3279867
  have eq3279955 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3261814 eq3279926
    | exact resolve eq3279926 eq3261814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261814 eq3279926
  have eq3279963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3249089 eq3279955
    | exact resolve eq3279955 eq3249089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249089 eq3279955
  have eq3279968 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq3279963
       have r₂ := eq27
       grind)
    | exact resolve eq3279963 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279963
  have eq3280798 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq3279968 eq212
    | exact resolve eq212 eq3279968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq3279968
  have eq3281042 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq387 eq3280798
    | (have j0 := eq3280798 (σ x)
       grind)
    | exact resolve eq3280798 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq3280798
  have eq3281094 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3249079 eq3281042
    | exact resolve eq3281042 eq3249079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249079 eq3281042
  have eq3283227 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3257406 eq3262406
    | exact resolve eq3262406 eq3257406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3257406 eq3262406
  have eq3283949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3281094 eq3283227
    | exact resolve eq3283227 eq3281094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281094 eq3283227
  have eq3284027 : False := by grind
  exact eq3284027

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X1))) = X0 := by
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
  clear eq22
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X1)) = (M.op X0 (M.op (M.op X0 (M.op X2 X1)) (M.op X3 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X2 X1)) (M.op X1 X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X3) (M.op X3 X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X0 (M.op X1 X2)) (M.op X2 X0)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) ≠ X0 ∨ (M.op X0 (M.op X2 X1)) = (M.op (M.op X0 (M.op X2 X1)) (M.op X1 X0)) ∨ (M.op X0 (M.op X2 X1)) = (k (M.op X1 X0) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X0) (M.op X0 (M.op X2 X1))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 X0) (M.op X0 (M.op X2 X1))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq44
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq44 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ x) (σ y)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq79
    | (have r₁ := eq79
       have r₂ := eq131
       grind)
    | exact resolve eq79 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq131
  have eq938 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq937
  have eq1009 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq938 eq122
    | exact resolve eq122 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq1013 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1009
  have eq1018 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1013
       have r₂ := eq133
       grind)
    | exact resolve eq1013 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1013
  have eq1038 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1018 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1018
       grind)
    | exact resolve eq13 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1051 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1038
  have eq1067 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1051
    | exact resolve eq1051 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1067 eq122
    | exact resolve eq122 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq1067
  have eq1077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1074
  have eq1081 : y = (M.op x y) := by
    first
    | (have r₁ := eq1077
       have r₂ := eq27
       grind)
    | exact resolve eq1077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1083 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1081 eq20
    | exact resolve eq20 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1099 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1083
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1083
    | exact resolve eq1083 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1153 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op X0 x) (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1260 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op X1 (M.op (M.op X0 x) y)))) := by
    intro X0 X1
    first
    | exact superpose eq1081 eq1153
    | exact resolve eq1153 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1264 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1099 eq26
    | exact resolve eq26 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1427 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (M.op y (M.op (M.op X0 x) (M.op x y))) ∨ y = (k (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq50 eq80
    | exact resolve eq80 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq80
  have eq1439 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 x) (M.op x y))) ∨ y = (k (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have j0 := eq1427 X0
       grind)
    | (have r₁ := eq1427 X0
       have r₂ := eq1081
       grind)
    | exact resolve eq1427 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1446 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 x) y)) ∨ y = (k (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq1081 eq1439
    | (have j0 := eq1439 X0
       grind)
    | exact resolve eq1439 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1453 : ∀ X0 : G, y = (k (M.op (M.op X0 x) y) y) ∨ y = (M.op y (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | exact superpose eq1081 eq1446
    | (have j0 := eq1446 X0
       grind)
    | exact resolve eq1446 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1470 : ∀ X2 : G, (M.op (M.op y X2) (M.op X2 y)) = X2 := by
    intro X2
    first
    | (have i₁ := eq55 y y (M.op x (M.op (M.op x x) y)) X2
       have i₂ := eq1260 x x
       grind)
    | exact superpose eq1260 eq55
    | exact resolve eq55 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1260
  have eq1523 : x = (M.op (M.op y x) (M.op x y)) := by
    first
    | (have i₁ := eq1470 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1470
    | (have j0 := eq1470 x
       grind)
    | exact resolve eq1470 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1548 : x = (M.op (M.op y x) y) := by
    first
    | exact superpose eq1081 eq1523
    | exact resolve eq1523 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq2124 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1453 y
       have i₂ := eq1548
       grind)
    | exact superpose eq1548 eq1453
    | exact resolve eq1453 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453 eq1548
  have eq2132 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2124
       grind)
    | exact superpose eq2124 eq44
    | exact resolve eq44 eq2124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq2139 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1099 eq2132
    | exact resolve eq2132 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132
  have eq2141 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2139
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2139
    | exact resolve eq2139 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139
  have eq2142 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1099 eq2141
    | exact resolve eq2141 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141
  have eq2145 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2142 eq96
    | (have j0 := eq96 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq96 eq2142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142
  have eq2146 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq2145
  have eq2148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1264 eq2146
    | exact resolve eq2146 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2151 : y = (M.op y x) := by
    first
    | (have r₁ := eq2148
       have r₂ := eq27
       grind)
    | exact resolve eq2148 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq2173 : y ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2151
       grind)
    | exact superpose eq2151 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2151
       grind)
    | exact resolve eq13 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq2189 : (M.op x y) = (k x y) := by grind
  clear eq2173
  have eq2191 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2189
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2189
    | exact resolve eq2189 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2189
  have eq2198 : y = (k x y) := by
    first
    | exact superpose eq1081 eq2191
    | exact resolve eq2191 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq2191
  have eq2254 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2198
       grind)
    | exact superpose eq2198 eq44
    | exact resolve eq44 eq2198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2198
  have eq2261 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1099 eq2254
    | exact resolve eq2254 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254
  have eq2263 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2261
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2261
    | exact resolve eq2261 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2261
  have eq2264 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1099 eq2263
    | exact resolve eq2263 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099 eq2263
  have eq2474 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2264 eq96
    | (have j0 := eq96 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq96 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2264
  have eq2475 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq2474
  have eq2477 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1264 eq2475
    | exact resolve eq2475 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq2475
  have eq2480 : False := by grind
  exact eq2480

/-- `Equation1672`: `x = (x ◇ y) ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1672 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1672 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1672.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq294 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq98 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq98 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq98 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq13 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq301 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq294 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq302 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq301 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq302 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq302
    | (have j0 := eq302 X0 X1
       grind)
    | exact resolve eq302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq310 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq830 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310
    | exact resolve eq310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq836 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq310 x y
       grind)
    | exact superpose eq310 eq16
    | (have j1 := eq310 x y
       grind)
    | exact resolve eq16 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq863 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq830 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq830
    | (have j0 := eq830 X0 X1
       grind)
    | exact resolve eq830 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq830
  have eq868 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq863 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq863
    | exact resolve eq863 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq1017 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq836
       have i₂ := eq868 x y
       grind)
    | exact superpose eq868 eq836
    | (have j1 := eq868 (σ x) (σ y)
       grind)
    | (have r₁ := eq836
       have r₂ := eq868 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq836
       have r₂ := eq868 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq836 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq868
  have eq1020 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1017
  have eq1022 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1020
       grind)
    | exact superpose eq1020 eq10
    | exact resolve eq10 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1057 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1022
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1022
    | exact resolve eq1022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1058 : x = y := by grind
  clear eq1057
  have eq1109 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1058
       grind)
    | exact superpose eq1058 eq16
    | exact resolve eq16 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1110 : False := by grind
  exact eq1110

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq22
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
  have eq74 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq75 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq44
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq127
  have eq704 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq703
  have eq707 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq704 eq118
    | exact resolve eq118 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq711 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq707
  have eq716 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq711
       have r₂ := eq129
       grind)
    | exact resolve eq711 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq711
  have eq720 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq716 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq716
       grind)
    | exact resolve eq13 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq744 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq720 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq744 eq118
    | exact resolve eq118 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq744
  have eq976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq972
  have eq981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq976
    | exact resolve eq976 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq983 : y = (M.op x y) := by
    first
    | (have r₁ := eq981
       have r₂ := eq27
       grind)
    | exact resolve eq981 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq985 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq983 eq20
    | exact resolve eq20 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq983 eq74
    | (have r₁ := eq74
       have r₂ := eq983
       grind)
    | exact resolve eq74 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq983
  have eq993 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq989
  have eq999 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq985
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq985
    | exact resolve eq985 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1000 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq999 eq26
    | exact resolve eq26 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1120 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq993
       grind)
    | exact superpose eq993 eq44
    | exact resolve eq44 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1127 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq999 eq1120
    | exact resolve eq1120 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1129 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1127
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1127
    | exact resolve eq1127 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1127
  have eq1130 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq999 eq1129
    | exact resolve eq1129 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1133 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1130 eq92
    | (have j0 := eq92 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1134 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by grind
  clear eq1133
  have eq1136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1000 eq1134
    | exact resolve eq1134 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1139 : y = (M.op y y) := by
    first
    | (have r₁ := eq1136
       have r₂ := eq27
       grind)
    | exact resolve eq1136 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1144 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1139
       grind)
    | exact superpose eq1139 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1139
       grind)
    | exact resolve eq13 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1166 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1193 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1166 x
       grind)
    | exact superpose eq1166 eq44
    | exact resolve eq44 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1166
  have eq1200 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq999 eq1193
    | exact resolve eq1193 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq1193
  have eq1204 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1200
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1200
    | exact resolve eq1200 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1200
  have eq1207 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1204
    | exact resolve eq1204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1204
  have eq1213 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1207 eq92
    | (have j0 := eq92 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1207
  have eq1214 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1213
  have eq1216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1000 eq1214
    | exact resolve eq1214 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq1214
  have eq1219 : False := by grind
  exact eq1219
