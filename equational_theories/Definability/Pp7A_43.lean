import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq42 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X1 (M.op X0 X0) X0 X2
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq42
    | exact resolve eq42 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq196 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq190 x y
       grind)
    | exact superpose eq190 eq16
    | (have j1 := eq190 y y
       grind)
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq70 (σ X0)
       have i₂ := eq190 X0 X0
       grind)
    | exact superpose eq190 eq70
    | (have j1 := eq190 X0 X0
       grind)
    | exact resolve eq70 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq190 X0 X1
       grind)
    | exact superpose eq190 eq9
    | (have j1 := eq190 X1 X1
       grind)
    | exact resolve eq9 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq190 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq363 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq345 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq412 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq360 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq360
    | (have j0 := eq360 (τ X0)
       grind)
    | exact resolve eq360 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq422 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq412 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq412
    | (have j0 := eq412 X0
       grind)
    | exact resolve eq412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq429 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq422 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq422
    | (have j0 := eq422 X0
       grind)
    | exact resolve eq422 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq521 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq36 x
       have i₂ := eq190 x x
       grind)
    | exact superpose eq190 eq36
    | (have j1 := eq190 X0 X0
       grind)
    | exact resolve eq36 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq538 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq521 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq549 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq538 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq538
    | (have j0 := eq538 X0
       grind)
    | exact resolve eq538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq696 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1396 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq549 (τ X0)
       grind)
    | exact superpose eq549 eq19
    | (have j1 := eq549 (τ X0)
       grind)
    | exact resolve eq19 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq549
  have eq1406 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1396 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1396
    | (have j0 := eq1396 X0
       grind)
    | exact resolve eq1396 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1422 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1406 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1406
    | (have j0 := eq1406 X0
       grind)
    | exact resolve eq1406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq1435 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1422 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1422
    | (have j0 := eq1422 X0
       grind)
    | exact resolve eq1422 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1460 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq1435 X0
       grind)
    | exact superpose eq1435 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq1435 X0
       grind)
    | exact resolve eq14 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq1471 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1926 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq363 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq363
    | (have j0 := eq363 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq363 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1935 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq363 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq363
    | exact resolve eq363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1975 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq1978 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1935 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1935
    | (have j0 := eq1935 X0
       grind)
    | exact resolve eq1935 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1935
  have eq1988 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1978 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1978
    | (have j0 := eq1978 X0
       grind)
    | exact resolve eq1978 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1978
  have eq2476 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq196 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq196
    | (have j0 := eq196 X0 X1
       grind)
    | exact resolve eq196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq2507 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2476 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2476
    | (have j0 := eq2476 X1 X1
       grind)
    | exact resolve eq2476 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2476
  have eq5996 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq341
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq341
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq341 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq5999 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq5996
  have eq6241 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X0)) X2) (σ (τ (k X0 X1)))) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq348 (τ X0) (τ X1) X2
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq348
    | (have j0 := eq348 (τ X1) (τ X1) X2
       grind)
    | exact resolve eq348 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq348
  have eq6339 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X0)) X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6241 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6241
    | (have j0 := eq6241 X1 X1 X2
       grind)
    | exact resolve eq6241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6241
  have eq6349 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6339 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6339
    | (have j0 := eq6339 X1 X1 X2
       grind)
    | exact resolve eq6339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339
  have eq6350 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6349 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6349
    | (have j0 := eq6349 X0 X1 X2
       grind)
    | exact resolve eq6349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6349
  have eq6351 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6350 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6350
    | (have j0 := eq6350 X0 X1 X2
       grind)
    | exact resolve eq6350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6350
  have eq6352 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6351 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6351
    | (have j0 := eq6351 X0 X1 X2
       grind)
    | exact resolve eq6351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6351
  have eq27631 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (k X0 X1)
       have i₂ := eq6352 X0 X1 X0
       grind)
    | exact superpose eq6352 eq76
    | (have j1 := eq6352 X1 X1 x
       grind)
    | exact resolve eq76 eq6352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6352
  have eq31589 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1988 X0
       have i₂ := eq1471 X0
       grind)
    | exact superpose eq1471 eq1988
    | (have j0 := eq1988 X0
       have j1 := eq1471 X0
       grind)
    | exact resolve eq1988 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471 eq1988
  have eq31678 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq31589 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31589
  have eq31710 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq31678 X0
       have j1 := eq429 X0
       grind)
    | (have r₁ := eq31678 X0
       have r₂ := eq429 X0
       grind)
    | exact resolve eq31678 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31678
  have eq31738 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31710 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq31710
    | (have j0 := eq31710 (σ X0)
       grind)
    | exact resolve eq31710 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31710
  have eq32119 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq89 (σ X0) (σ X0)
       have i₂ := eq31738 X0
       grind)
    | exact superpose eq31738 eq89
    | (have j1 := eq31738 X0
       grind)
    | exact resolve eq89 eq31738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31738
  have eq50740 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq5999
       grind)
    | exact superpose eq5999 eq36
    | exact resolve eq36 eq5999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5999
  have eq50904 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50740
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq50740
    | exact resolve eq50740 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50740
  have eq50911 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq429 y
       grind)
    | (have r₁ := eq50904
       have r₂ := eq429 y
       grind)
    | exact resolve eq50904 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq50904
  have eq50928 : (k (τ (σ y)) y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq193 (σ y) y
       have i₂ := eq50911
       grind)
    | exact superpose eq50911 eq193
    | exact resolve eq193 eq50911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq50930 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  have eq50931 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70 (σ y)
       have i₂ := eq50911
       grind)
    | exact superpose eq50911 eq70
    | exact resolve eq70 eq50911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50911
  have eq51046 : (k (τ (σ y)) y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq50928
  have eq51057 : (σ x) = (σ (k x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50930
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq50930
    | exact resolve eq50930 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50930
  have eq51058 : x = (k (τ (σ y)) y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51046
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq51046
    | exact resolve eq51046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51046
  have eq51065 : x = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51058
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq51058
    | exact resolve eq51058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51058
  have eq51365 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2507 x y
       have i₂ := eq51057
       grind)
    | exact superpose eq51057 eq2507
    | (have j0 := eq2507 y y
       grind)
    | exact resolve eq2507 eq51057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507 eq51057
  have eq51424 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq51365
  have eq53335 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50931
       grind)
    | exact superpose eq50931 eq16
    | exact resolve eq16 eq50931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50931
  have eq53427 : (σ x) ≠ (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53335
       have i₂ := eq51424
       grind)
    | exact superpose eq51424 eq53335
    | exact resolve eq53335 eq51424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51424 eq53335
  have eq53428 : (σ x) ≠ (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq53427
  have eq64285 : y = (M.op y y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq51065
       have r₂ := eq53428
       grind)
    | exact resolve eq51065 eq53428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51065 eq53428
  have eq64307 : y = (k y y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq64285
  have eq64510 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq64307
       have i₂ := eq14 y y
       grind)
    | exact superpose eq14 eq64307
    | (have j1 := eq14 y y
       grind)
    | exact resolve eq64307 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64307
  have eq64630 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq64510
  have eq64659 : y = (k y y) ∨ x = (M.op y y) := by grind
  have eq64663 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq64630
       grind)
    | exact superpose eq64630 eq76
    | exact resolve eq76 eq64630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64755 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq696 y y x
       have i₂ := eq64630
       grind)
    | exact superpose eq64630 eq696
    | exact resolve eq696 eq64630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64630
  have eq64816 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq64755 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq64755
    | exact resolve eq64755 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64755
  have eq64864 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq363 y
       have i₂ := eq64659
       grind)
    | exact superpose eq64659 eq363
    | (have j0 := eq363 y
       grind)
    | exact resolve eq363 eq64659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq64659
  have eq64979 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq64864
  have eq65568 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq76 (σ y) X0
       have i₂ := eq64979
       grind)
    | exact superpose eq64979 eq76
    | exact resolve eq76 eq64979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq65660 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq696 (σ y) (σ y) x
       have i₂ := eq64979
       grind)
    | exact superpose eq64979 eq696
    | exact resolve eq696 eq64979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq64979
  have eq65723 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq65660 X0
       have i₂ := eq89 (σ y) X0
       grind)
    | exact superpose eq89 eq65660
    | exact resolve eq65660 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65660
  have eq65905 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq64663 X0
       have i₂ := eq64816 X0
       grind)
    | exact superpose eq64816 eq64663
    | exact resolve eq64663 eq64816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64663
  have eq66095 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq65905 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65905
  have eq66194 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 y y
       have i₂ := eq66095 X0
       grind)
    | exact superpose eq66095 eq89
    | (have j1 := eq66095 x
       grind)
    | exact resolve eq89 eq66095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66276 : x ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq66095 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66095
  have eq67123 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq66194 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66194
  have eq67124 : x = (M.op y x) := by grind
  clear eq67123
  have eq67146 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64816 x
       have i₂ := eq67124
       grind)
    | exact superpose eq67124 eq64816
    | exact resolve eq64816 eq67124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64816
  have eq67148 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq67124
       grind)
    | exact superpose eq67124 eq9
    | exact resolve eq9 eq67124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67124
  have eq78367 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq65568 X0
       have i₂ := eq65723 X0
       grind)
    | exact superpose eq65723 eq65568
    | exact resolve eq65568 eq65723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65568
  have eq78574 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq78367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78367
  have eq78600 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq65723 X0
       have i₂ := eq78574 X0
       grind)
    | exact superpose eq78574 eq65723
    | exact resolve eq65723 eq78574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65723 eq78574
  have eq78916 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq78600 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78600
  have eq79504 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78916 (σ x)
       grind)
    | exact superpose eq78916 eq16
    | exact resolve eq16 eq78916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78916
  have eq79608 : (σ y) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79504
       have i₂ := eq67146
       grind)
    | exact superpose eq67146 eq79504
    | exact resolve eq79504 eq67146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67146 eq79504
  have eq79618 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq79608
  have eq79619 : x = (M.op y y) := by grind
  clear eq79618
  have eq79662 : x = (k x y) := by grind
  have eq79663 : y = (M.op x y) := by
    first
    | (have i₁ := eq70 y
       have i₂ := eq79619
       grind)
    | exact superpose eq79619 eq70
    | exact resolve eq70 eq79619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq79703 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq79619
       grind)
    | exact superpose eq79619 eq9
    | exact resolve eq9 eq79619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1709806 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1975 y
       have i₂ := eq79619
       grind)
    | exact superpose eq79619 eq1975
    | (have j0 := eq1975 y
       grind)
    | exact resolve eq1975 eq79619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq1710861 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq1709806
       grind)
    | exact superpose eq1709806 eq36
    | exact resolve eq36 eq1709806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1709806
  have eq1712016 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1710861
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1710861
    | exact resolve eq1710861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710861
  have eq1712036 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1712016
       grind)
    | exact superpose eq1712016 eq16
    | exact resolve eq16 eq1712016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712016
  have eq1712837 : (σ y) ≠ (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1712036
       have i₂ := eq79663
       grind)
    | exact superpose eq79663 eq1712036
    | exact resolve eq1712036 eq79663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79663 eq1712036
  have eq1712838 : y = (k y y) ∨ x = y := by grind
  clear eq1712837
  have eq1713670 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq27631 y y
       have i₂ := eq1712838
       grind)
    | exact superpose eq1712838 eq27631
    | (have j0 := eq27631 y y
       grind)
    | exact resolve eq27631 eq1712838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27631 eq1712838
  have eq1713673 : y = (M.op y y) ∨ x = y := by grind
  clear eq1713670
  have eq1714143 : y = (M.op y y) := by
    first
    | (have r₁ := eq1713673
       have r₂ := eq66276
       grind)
    | exact resolve eq1713673 eq66276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66276 eq1713673
  have eq1714519 : x = y := by
    first
    | (have i₁ := eq1714143
       have i₂ := eq79619
       grind)
    | exact superpose eq79619 eq1714143
    | exact resolve eq1714143 eq79619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79619 eq1714143
  have eq1714811 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1714519
       grind)
    | exact superpose eq1714519 eq16
    | exact resolve eq16 eq1714519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1714910 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq67148 X0
       have i₂ := eq1714519
       grind)
    | exact superpose eq1714519 eq67148
    | exact resolve eq67148 eq1714519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67148
  have eq1714991 : x = (k x x) := by
    first
    | (have i₁ := eq79662
       have i₂ := eq1714519
       grind)
    | exact superpose eq1714519 eq79662
    | exact resolve eq79662 eq1714519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79662
  have eq1715030 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq79703 X0
       have i₂ := eq1714519
       grind)
    | exact superpose eq1714519 eq79703
    | exact resolve eq79703 eq1714519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79703 eq1714519
  have eq1715153 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1715030 X0
       have i₂ := eq89 x X0
       grind)
    | exact superpose eq89 eq1715030
    | exact resolve eq1715030 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1715030
  have eq1716440 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32119 x
       have i₂ := eq1714991
       grind)
    | exact superpose eq1714991 eq32119
    | (have j0 := eq32119 x
       grind)
    | exact resolve eq32119 eq1714991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32119 eq1714991
  have eq1717036 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1716440
  have eq1721109 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1714910 X0
       have i₂ := eq1715153 X0
       grind)
    | exact superpose eq1715153 eq1714910
    | exact resolve eq1714910 eq1715153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714910
  have eq1721155 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1715153 X0
       have i₂ := eq1721109 X0
       grind)
    | exact superpose eq1721109 eq1715153
    | exact resolve eq1715153 eq1721109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715153 eq1721109
  have eq1760591 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1714811
       have i₂ := eq1721155 x
       grind)
    | exact superpose eq1721155 eq1714811
    | exact resolve eq1714811 eq1721155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714811 eq1721155
  have eq1760592 : False := by grind
  exact eq1760592

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
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
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq74 y x
       grind)
    | exact superpose eq74 eq71
    | (have j1 := eq74 y x
       grind)
    | exact resolve eq71 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq106 eq74
    | (have j0 := eq74 (σ y) x
       grind)
    | exact resolve eq74 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq700
    | exact resolve eq700 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq704 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq701
       have r₂ := eq27
       grind)
    | exact resolve eq701 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq715 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq704 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq704
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq704
       grind)
    | exact resolve eq13 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq715 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq732 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq716 eq84
    | exact resolve eq84 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq716
  have eq772 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq704 eq732
    | exact resolve eq732 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq732
  have eq785 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq772
  have eq787 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq785
    | exact resolve eq785 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq785
  have eq790 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74 y y
       have i₂ := eq787
       grind)
    | exact superpose eq787 eq74
    | (have j0 := eq74 y x
       grind)
    | exact resolve eq74 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq791 : y = (M.op y y) := by grind
  clear eq790
  have eq794 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq791
       grind)
    | exact superpose eq791 eq14
    | exact resolve eq14 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq791
       grind)
    | exact superpose eq791 eq14
    | exact resolve eq14 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq791
       grind)
    | exact superpose eq791 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq791
       grind)
    | exact resolve eq13 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq803 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq819 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq804 x
       grind)
    | exact superpose eq804 eq44
    | exact resolve eq44 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq821 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq804 y
       grind)
    | exact superpose eq804 eq72
    | exact resolve eq72 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq804
  have eq828 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq821
       have i₂ := eq791
       grind)
    | exact superpose eq791 eq821
    | exact resolve eq821 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq821
  have eq829 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq828
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq828
    | exact resolve eq828 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq834 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq829 eq74
    | (have j0 := eq74 (σ y) x
       grind)
    | exact resolve eq74 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq829
  have eq835 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq834
  have eq859 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq835 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq835
       grind)
    | exact resolve eq13 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq860 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq859 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq890 : (σ (M.op y x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq860 eq819
    | exact resolve eq819 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq860
  have eq993 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq795 (M.op y X0)
       have i₂ := eq794 X0
       grind)
    | exact superpose eq794 eq795
    | exact resolve eq795 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq794 X0
       have i₂ := eq993 X0
       grind)
    | exact superpose eq993 eq794
    | exact resolve eq794 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq993
  have eq1057 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq795 X0
       have i₂ := eq1043 X0
       grind)
    | exact superpose eq1043 eq795
    | exact resolve eq795 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq1065 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1043 X0
       have i₂ := eq1057 X0
       grind)
    | exact superpose eq1057 eq1043
    | exact resolve eq1043 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1071 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq890
       have i₂ := eq1057 x
       grind)
    | exact superpose eq1057 eq890
    | exact resolve eq890 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq1075 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 y X0
       have i₂ := eq1057 X0
       grind)
    | exact superpose eq1057 eq14
    | exact resolve eq14 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1075 X0 X1
       have i₂ := eq1057 X1
       grind)
    | exact superpose eq1057 eq1075
    | exact resolve eq1075 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq1075
  have eq1098 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1071
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1071
    | exact resolve eq1071 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1071
  have eq1099 : y = (M.op x y) := by
    first
    | (have i₁ := eq1065 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1065
    | (have j0 := eq1065 x
       grind)
    | exact resolve eq1065 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1065
  have eq1162 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1099 eq20
    | exact resolve eq20 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1099
  have eq1195 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1162
    | exact resolve eq1162 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1162
  have eq1207 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1195 eq26
    | exact resolve eq26 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1244 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1195 eq1098
    | exact resolve eq1098 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq1195
  have eq1423 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1244 eq1095
    | exact resolve eq1095 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095 eq1244
  have eq1449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1207 eq1423
    | exact resolve eq1423 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207 eq1423
  have eq1461 : False := by grind
  exact eq1461

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq67 (M.op X0 X1)
       grind)
    | exact superpose eq67 eq61
    | exact resolve eq61 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq61
    | exact resolve eq61 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 X1) X0 X2 X3
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq62
    | exact resolve eq62 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq277 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq161 y x
       grind)
    | exact superpose eq161 eq16
    | (have j1 := eq161 y y
       grind)
    | exact resolve eq16 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X1) X2
       have i₂ := eq161 X0 X1
       grind)
    | exact superpose eq161 eq9
    | (have j1 := eq161 X0 X0
       grind)
    | exact resolve eq9 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq161 X0 X0
       grind)
    | exact superpose eq161 eq67
    | (have j1 := eq161 X0 X0
       grind)
    | exact resolve eq67 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq161
  have eq299 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq570 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1299 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq299 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq299
    | exact resolve eq299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq1333 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1299 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1299
    | (have j0 := eq1299 X0
       grind)
    | exact resolve eq1299 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1299
  have eq1337 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1333 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1333
    | (have j0 := eq1333 X0
       grind)
    | exact resolve eq1333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1344 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1337 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq1337
    | (have j0 := eq1337 (τ X0)
       grind)
    | exact resolve eq1337 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5551 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq277
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq277
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq277 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq5554 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq5551
  have eq6510 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X1)) X2)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq278 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq278
    | (have j0 := eq278 (τ X0) (τ X0) X2
       grind)
    | exact resolve eq278 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq278
  have eq6635 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X1)) X2)) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6510 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6510
    | (have j0 := eq6510 X0 X0 X2
       grind)
    | exact resolve eq6510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6510
  have eq6646 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op X1 X2)) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6635 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6635
    | (have j0 := eq6635 X0 X0 X2
       grind)
    | exact resolve eq6635 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6635
  have eq6655 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X1 X2)) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6646 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6646
    | (have j0 := eq6646 X0 X0 X2
       grind)
    | exact resolve eq6646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6646
  have eq6664 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (k X0 X1) (M.op X1 X2)) X0) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6655 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6655
    | (have j0 := eq6655 X0 X1 X2
       grind)
    | exact resolve eq6655 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655
  have eq6669 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X1 X2)) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6664 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6664
    | (have j0 := eq6664 X0 X1 X2
       grind)
    | exact resolve eq6664 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6664
  have eq10254 : ∀ X0 X1 : G, (k X0 X1) = (M.op (M.op (k X0 X1) X0) (k X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83 (k X0 X1) X1 X0
       have i₂ := eq6669 X0 X1 (k X0 X1)
       grind)
    | exact superpose eq6669 eq83
    | (have j1 := eq6669 X0 X0 x
       grind)
    | exact resolve eq83 eq6669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq6669
  have eq17258 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq5554
       grind)
    | exact superpose eq5554 eq12
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq5554
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq5554
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq5554
       grind)
    | exact resolve eq12 eq5554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5554
  have eq17374 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq17258 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17258
  have eq26483 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10254 X0 X0
       have i₂ := eq1337 X0
       grind)
    | exact superpose eq1337 eq10254
    | (have j0 := eq10254 X0 X0
       have j1 := eq1337 X0
       grind)
    | exact resolve eq10254 eq1337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337 eq10254
  have eq26613 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26483 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26483
  have eq26616 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26613 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq26613
    | (have j0 := eq26613 (σ X0)
       grind)
    | exact resolve eq26613 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26613
  have eq126856 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ (σ y) = (k X1 (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq17374 X0
       grind)
    | exact superpose eq17374 eq12
    | (have j1 := eq17374 X1
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq17374 X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq17374 X0
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq17374 X0
       grind)
    | exact resolve eq12 eq17374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17374
  have eq127084 : ∀ X0 X1 : G, (σ y) = (k X1 (σ y)) ∨ (σ x) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq126856 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126856
  have eq127220 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1344 (σ y)
       have i₂ := eq127084 X0 (σ y)
       grind)
    | exact superpose eq127084 eq1344
    | (have j0 := eq1344 (σ y)
       have j1 := eq127084 X0 x
       grind)
    | exact resolve eq1344 eq127084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127084
  have eq127451 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq127220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127220
  have eq127537 : ∀ X0 : G, y = (M.op y y) ∨ (σ x) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq127451 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq127451
    | (have j0 := eq127451 X0
       grind)
    | exact resolve eq127451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127451
  have eq127538 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq127537 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127537
  have eq129985 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1344 (σ x)
       have i₂ := eq127538 (σ x)
       grind)
    | exact superpose eq127538 eq1344
    | (have j0 := eq1344 (σ x)
       grind)
    | exact resolve eq1344 eq127538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344 eq127538
  have eq130216 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq129985
  have eq130302 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq130216
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq130216
    | exact resolve eq130216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130216
  have eq130303 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq130302
  have eq130375 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq130303
       grind)
    | exact superpose eq130303 eq12
    | (have r₁ := eq12 X0 y
       have r₂ := eq130303
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq130303
       grind)
    | exact resolve eq12 eq130303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130380 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq130303
       grind)
    | exact superpose eq130303 eq73
    | exact resolve eq73 eq130303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130511 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq570 y y x
       have i₂ := eq130303
       grind)
    | exact superpose eq130303 eq570
    | exact resolve eq570 eq130303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130303
  have eq130607 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq130375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130375
  have eq130637 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq130511 X0
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq130511
    | exact resolve eq130511 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130511
  have eq133157 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26616 y
       have i₂ := eq130607 y
       grind)
    | exact superpose eq130607 eq26616
    | (have j0 := eq26616 y
       grind)
    | exact resolve eq26616 eq130607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130607
  have eq133338 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq133157
  have eq136869 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq73 (σ y) X0
       have i₂ := eq133338
       grind)
    | exact superpose eq133338 eq73
    | exact resolve eq73 eq133338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133338
  have eq140888 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq130380 X0
       have i₂ := eq130637 X0
       grind)
    | exact superpose eq130637 eq130380
    | exact resolve eq130380 eq130637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130380 eq130637
  have eq141314 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq140888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140888
  have eq141351 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq141314 X1
       grind)
    | exact superpose eq141314 eq73
    | (have j1 := eq141314 X1
       grind)
    | exact resolve eq73 eq141314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141482 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq570 x x x
       have i₂ := eq141314 X0
       grind)
    | exact superpose eq141314 eq570
    | (have j1 := eq141314 X1
       grind)
    | exact resolve eq570 eq141314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141314
  have eq141626 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141482 X0 X1
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq141482
    | (have j0 := eq141482 X0 X1
       grind)
    | exact resolve eq141482 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141482
  have eq151739 : ∀ X0 X1 X2 : G, (M.op x X0) = X0 ∨ (M.op y X1) = X1 ∨ (M.op y X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141351 X0 X1
       have i₂ := eq141626 X0 X2
       grind)
    | exact superpose eq141626 eq141351
    | (have j0 := eq141351 X0 X1
       have j1 := eq141626 X0 X1
       grind)
    | exact resolve eq141351 eq141626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141351 eq141626
  have eq152178 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq151739 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151739
  have eq152218 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 y X0
       have i₂ := eq152178 y X1
       grind)
    | exact superpose eq152178 eq74
    | (have j1 := eq152178 X0 X1
       grind)
    | exact resolve eq74 eq152178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq152260 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 y X1
       have i₂ := eq152178 X0 X2
       grind)
    | exact superpose eq152178 eq9
    | (have j1 := eq152178 X0 X2
       grind)
    | exact resolve eq9 eq152178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152901 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152218 X0 X1
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq152218
    | (have j0 := eq152218 X0 X1
       grind)
    | exact resolve eq152218 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152218
  have eq156920 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152901 X0 X1
       have i₂ := eq152178 X0 X2
       grind)
    | exact superpose eq152178 eq152901
    | (have j0 := eq152901 X0 X1
       have j1 := eq152178 X0 X1
       grind)
    | exact resolve eq152901 eq152178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152901
  have eq157495 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq156920 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156920
  have eq158866 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq157495 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157495
  have eq158867 : y = (M.op x y) := by grind
  clear eq158866
  have eq172922 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (M.op x X2) = X2 ∨ (M.op x X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq152260 X1 X0 X2
       have i₂ := eq152178 X0 X3
       grind)
    | exact superpose eq152178 eq152260
    | (have j0 := eq152260 X0 X1 X2
       have j1 := eq152178 X0 X2
       grind)
    | exact resolve eq152260 eq152178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152178 eq152260
  have eq173939 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq172922 X2 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172922
  have eq234736 : ∀ X0 X1 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136869 X0
       have i₂ := eq173939 X1 (σ y) X0
       grind)
    | exact superpose eq173939 eq136869
    | (have j1 := eq173939 x X1 x
       grind)
    | exact resolve eq136869 eq173939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136869
  have eq235270 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq234736 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234736
  have eq235697 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x X1) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq173939 X1 (σ y) X0
       have i₂ := eq235270 X0
       grind)
    | exact superpose eq235270 eq173939
    | (have j0 := eq173939 X1 X1 x
       grind)
    | exact resolve eq173939 eq235270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173939 eq235270
  have eq236144 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq235697 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235697
  have eq237643 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq236144 (σ x)
       grind)
    | exact superpose eq236144 eq16
    | exact resolve eq16 eq236144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236144
  have eq237887 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq237643
       have i₂ := eq158867
       grind)
    | exact superpose eq158867 eq237643
    | exact resolve eq237643 eq158867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237643
  have eq237888 : x = (M.op x x) := by grind
  clear eq237887
  have eq237919 : ∀ X0 : G, x ≠ x ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq237888
       grind)
    | exact superpose eq237888 eq12
    | (have r₁ := eq12 X0 x
       have r₂ := eq237888
       grind)
    | exact resolve eq12 eq237888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237924 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq237888
       grind)
    | exact superpose eq237888 eq73
    | exact resolve eq73 eq237888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq238055 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq570 x x x
       have i₂ := eq237888
       grind)
    | exact superpose eq237888 eq570
    | exact resolve eq570 eq237888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237888
  have eq238210 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq237919 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237919
  have eq238270 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq238055 X0
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq238055
    | exact resolve eq238055 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq238055
  have eq238397 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26616 x
       have i₂ := eq238210 x
       grind)
    | exact superpose eq238210 eq26616
    | (have j0 := eq26616 x
       grind)
    | exact resolve eq26616 eq238210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26616 eq238210
  have eq238595 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq238397
  have eq247396 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq237924 X0
       have i₂ := eq238270 X0
       grind)
    | exact superpose eq238270 eq237924
    | exact resolve eq237924 eq238270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237924 eq238270
  have eq249038 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op x X1) X0) X2) (M.op x X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq205 x X1 X0 X2
       have i₂ := eq247396 X0
       grind)
    | exact superpose eq247396 eq205
    | exact resolve eq205 eq247396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq249098 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 x X1 X0
       have i₂ := eq247396 X0
       grind)
    | exact superpose eq247396 eq570
    | exact resolve eq570 eq247396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq250086 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq249098 X0 X0
       have i₂ := eq247396 X0
       grind)
    | exact superpose eq247396 eq249098
    | exact resolve eq249098 eq247396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249098
  have eq250140 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq249038 X0 X0 X2
       have i₂ := eq247396 X0
       grind)
    | exact superpose eq247396 eq249038
    | exact resolve eq249038 eq247396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247396 eq249038
  have eq318722 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq250140 (σ x) (σ x) X0
       have i₂ := eq238595
       grind)
    | exact superpose eq238595 eq250140
    | exact resolve eq250140 eq238595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238595 eq250140
  have eq320254 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq318722 X0
       have i₂ := eq250086 X0 (σ x)
       grind)
    | exact superpose eq250086 eq318722
    | exact resolve eq318722 eq250086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250086 eq318722
  have eq321561 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq320254 (σ y)
       grind)
    | exact superpose eq320254 eq16
    | exact resolve eq16 eq320254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320254
  have eq322694 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq321561
       have i₂ := eq158867
       grind)
    | exact superpose eq158867 eq321561
    | exact resolve eq321561 eq158867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158867 eq321561
  have eq322695 : False := by grind
  exact eq322695

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_y_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  clear eq43
  have eq59 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq211 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq378 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq14
    | exact resolve eq14 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq14
    | exact resolve eq14 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq61 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq64 X3 X2 X4 X0
       grind)
    | exact superpose eq64 eq61
    | exact resolve eq61 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq693 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq378 (σ X0)
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq378
    | (have j1 := eq74 X0 X0
       grind)
    | exact resolve eq378 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq704 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq705 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq704 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq708 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq693 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq868 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq386
    | exact resolve eq386 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq62 eq386
    | exact resolve eq386 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63 eq386
    | exact resolve eq386 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op x X0)
       have i₂ := eq868 x X0
       grind)
    | exact superpose eq868 eq62
    | exact resolve eq62 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq972 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (M.op sF2 x)
       have i₂ := eq868 sF2 x
       grind)
    | exact superpose eq868 eq63
    | exact resolve eq63 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq984 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op (M.op y (M.op (M.op (M.op x y) (M.op x X1)) X2)) X0) y) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq211 eq61
    | exact resolve eq61 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq211
  have eq3516 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq705 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq705
    | (have j0 := eq705 (τ X0)
       grind)
    | exact resolve eq705 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3524 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3516 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3516
    | (have j0 := eq3516 X0
       grind)
    | exact resolve eq3516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3516
  have eq3530 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3524 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3524
    | (have j0 := eq3524 X0
       grind)
    | exact resolve eq3524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524
  have eq10838 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq457 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq14 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq14 eq457
    | exact resolve eq457 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq10878 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq10838 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq10838
    | exact resolve eq10838 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10838
  have eq26414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq26424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq26414
    | exact resolve eq26414 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26414
  have eq26435 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq26424
       have r₂ := eq27
       grind)
    | exact resolve eq26424 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26424
  have eq26484 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26435 eq868
    | exact resolve eq868 eq26435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26435
  have eq26527 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26484 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq26484
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq26484
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq26484
       grind)
    | exact resolve eq13 eq26484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26484
  have eq26574 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq26527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26527
  have eq26779 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26574 eq346
    | exact resolve eq346 eq26574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26574
  have eq26804 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ y = (k X0 y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq26779
    | exact resolve eq26779 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq26779
  have eq26883 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ y = (k X1 y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq26804 eq13
    | (have j0 := eq13 X0 (σ x)
       have j1 := eq26804 X1
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq26804 X0
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq26804 X0
       grind)
    | exact resolve eq13 eq26804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26804
  have eq26930 : ∀ X0 X1 : G, (σ x) = (k X0 (σ x)) ∨ y = (k X1 y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq26883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26883
  have eq27111 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ y = (k X0 y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26930 eq49
    | (have j1 := eq26930 X0 X0
       grind)
    | exact resolve eq49 eq26930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq27154 : ∀ X0 X1 : G, (τ (σ x)) = (k X0 (τ (σ x))) ∨ y = (k X1 y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq26930 eq346
    | (have j1 := eq26930 X0 X1
       grind)
    | exact resolve eq346 eq26930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq26930
  have eq27181 : ∀ X0 X1 : G, x = (k X0 x) ∨ y = (k X1 y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq28 eq27154
    | (have j0 := eq27154 X0 X1
       grind)
    | exact resolve eq27154 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27154
  have eq27203 : ∀ X0 : G, x = (k x x) ∨ y = (k X0 y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq27111
    | (have j0 := eq27111 X0
       grind)
    | exact resolve eq27111 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq27111
  have eq27232 : ∀ X0 X1 : G, y = (k X1 y) ∨ x = (k X0 x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq27181 X0 X1
       have j1 := eq13 X1 y
       grind)
    | (have r₁ := eq27181 X0 X1
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq27181 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27181
  have eq27237 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq27203 X0
       have j1 := eq3530 x
       grind)
    | (have r₁ := eq27203 X0
       have r₂ := eq3530 x
       grind)
    | (have r₁ := eq27203 y
       have r₂ := eq3530 y
       grind)
    | exact resolve eq27203 eq3530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27203
  have eq27293 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ x = (k X0 x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq3530 y
       have i₂ := eq27232 X0 y
       grind)
    | exact superpose eq27232 eq3530
    | (have j0 := eq3530 y
       have j1 := eq27232 X0 x
       grind)
    | (have r₁ := eq3530 y
       have r₂ := eq27232 X0 y
       grind)
    | (have r₁ := eq3530 x
       have r₂ := eq27232 x x
       grind)
    | exact resolve eq3530 eq27232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27232
  have eq27329 : ∀ X0 : G, y = (M.op y y) ∨ x = (k X0 x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq27293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27293
  have eq27522 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3530 y
       have i₂ := eq27237 y
       grind)
    | exact superpose eq27237 eq3530
    | (have j0 := eq3530 y
       grind)
    | (have r₁ := eq3530 y
       have r₂ := eq27237 y
       grind)
    | exact resolve eq3530 eq27237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27237
  have eq27558 : y = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq27522
  have eq27648 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k X1 x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq386 y X0
       have i₂ := eq27329 X1
       grind)
    | exact superpose eq27329 eq386
    | (have j1 := eq27329 X1
       grind)
    | exact resolve eq386 eq27329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27329
  have eq28201 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq27558
       grind)
    | exact superpose eq27558 eq14
    | exact resolve eq14 eq27558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27558
  have eq28266 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28201 X0
       have i₂ := eq868 y X0
       grind)
    | exact superpose eq868 eq28201
    | exact resolve eq28201 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28201
  have eq36291 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ x = (k X1 x) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq27648 X0 X1
       have i₂ := eq28266 X0
       grind)
    | exact superpose eq28266 eq27648
    | (have j0 := eq27648 X0 X1
       grind)
    | exact resolve eq27648 eq28266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27648 eq28266
  have eq36384 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ x = (k X1 x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq36291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36291
  have eq36394 : ∀ X0 X1 : G, y = (M.op y x) ∨ x = (k X1 x) ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq36384 X0 X1
       have j1 := eq13 X1 x
       grind)
    | (have r₁ := eq36384 y X1
       have r₂ := eq13 X0 y
       grind)
    | (have r₁ := eq36384 X0 X1
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq36384 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36384
  have eq36506 : ∀ X0 X1 : G, y = (M.op y y) ∨ x = (k X0 x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq868 y x
       have i₂ := eq36394 X0 X1
       grind)
    | exact superpose eq36394 eq868
    | (have j1 := eq36394 y X0
       grind)
    | exact resolve eq868 eq36394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36394
  have eq36670 : ∀ X0 : G, y ≠ y ∨ x = (k X0 x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq36506 X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36506
  have eq36671 : ∀ X0 : G, y = (M.op y y) ∨ x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq36670 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36670
  have eq36707 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq386 y X0
       have i₂ := eq36671 X1
       grind)
    | exact superpose eq36671 eq386
    | (have j1 := eq36671 X1
       grind)
    | exact resolve eq386 eq36671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36758 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq10878 y y x
       have i₂ := eq36671 X0
       grind)
    | exact superpose eq36671 eq10878
    | (have j1 := eq36671 X1
       grind)
    | exact resolve eq10878 eq36671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10878 eq36671
  have eq36761 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ x = (k X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq36758 X0 X1
       have i₂ := eq868 y X0
       grind)
    | exact superpose eq868 eq36758
    | (have j0 := eq36758 X0 X1
       grind)
    | exact resolve eq36758 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36758
  have eq40490 : ∀ X0 X1 X2 : G, x = (k X2 x) ∨ x = (k X1 x) ∨ (M.op y X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36707 X0 X2
       have i₂ := eq36761 X0 X1
       grind)
    | exact superpose eq36761 eq36707
    | (have j0 := eq36707 X0 X2
       have j1 := eq36761 X0 X2
       grind)
    | exact resolve eq36707 eq36761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36707 eq36761
  have eq110448 : ∀ X0 X1 : G, x ≠ x ∨ x = (k X0 x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq40490 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40490
  have eq110449 : ∀ X0 X1 : G, x = (k X0 x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq110448 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110448
  have eq111581 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3530 x
       have i₂ := eq110449 x X0
       grind)
    | exact superpose eq110449 eq3530
    | (have j0 := eq3530 x
       have j1 := eq110449 X0 X0
       grind)
    | (have r₁ := eq3530 x
       have r₂ := eq110449 x x
       grind)
    | exact resolve eq3530 eq110449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530
  have eq111582 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq705 x
       have i₂ := eq110449 x X0
       grind)
    | exact superpose eq110449 eq705
    | (have j0 := eq705 x
       have j1 := eq110449 X0 X0
       grind)
    | exact resolve eq705 eq110449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq110449
  have eq111680 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq111582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111582
  have eq111681 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq111581 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111581
  have eq111772 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq111680 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq111680
    | (have j0 := eq111680 X0
       grind)
    | exact resolve eq111680 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq111680
  have eq111946 : ∀ X0 : G, y = (M.op (M.op (M.op x y) x) y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 x
       have i₂ := eq111681 X0
       grind)
    | exact superpose eq111681 eq59
    | (have j1 := eq111681 X0
       grind)
    | exact resolve eq59 eq111681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq111967 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq970 x
       have i₂ := eq111681 X0
       grind)
    | exact superpose eq111681 eq970
    | (have j1 := eq111681 X0
       grind)
    | exact resolve eq970 eq111681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq111681
  have eq112054 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq870 eq111967
    | (have j0 := eq111967 X0
       grind)
    | exact resolve eq111967 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq111967
  have eq113014 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq111772 (M.op sF2 X0)
       grind)
    | exact superpose eq111772 eq60
    | (have j1 := eq111772 X0
       grind)
    | exact resolve eq60 eq111772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq113035 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq972 X0
       have i₂ := eq111772 (M.op sF2 X0)
       grind)
    | exact superpose eq111772 eq972
    | (have j1 := eq111772 X0
       grind)
    | exact resolve eq972 eq111772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq111772
  have eq113124 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq872 eq113035
    | (have j0 := eq113035 X0
       grind)
    | exact resolve eq113035 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq113035
  have eq119601 : ∀ X0 X1 : G, y = (M.op x y) ∨ (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq111946 X0
       have i₂ := eq112054 (M.op sF0 x)
       grind)
    | exact superpose eq112054 eq111946
    | (have j0 := eq111946 X0
       have j1 := eq112054 X0
       grind)
    | exact resolve eq111946 eq112054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111946 eq112054
  have eq119668 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq119601 X1 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119601
    | (have j0 := eq119601 X1 X1
       grind)
    | exact resolve eq119601 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119601
  have eq132763 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq119668 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119668
  have eq132764 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq132763 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132763
  have eq132804 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq387 y X0
       have i₂ := eq132764 y
       grind)
    | exact superpose eq132764 eq387
    | exact resolve eq387 eq132764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132935 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq132804 X0
       have i₂ := eq868 y X0
       grind)
    | exact superpose eq868 eq132804
    | exact resolve eq132804 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868 eq132804
  have eq137838 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq132935 X0
       have i₂ := eq132764 X0
       grind)
    | exact superpose eq132764 eq132935
    | exact resolve eq132935 eq132764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132764 eq132935
  have eq137958 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq137838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137838
  have eq138252 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq137958 x
       grind)
    | exact superpose eq137958 eq18
    | (have j1 := eq137958 x
       grind)
    | exact resolve eq18 eq137958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq137958
  have eq138347 : y = (M.op x y) := by grind
  clear eq138252
  have eq138357 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq138347 eq20
    | exact resolve eq20 eq138347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq138347
  have eq138707 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq138357
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq138357
    | exact resolve eq138357 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138357
  have eq138709 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq138707 eq26
    | exact resolve eq26 eq138707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq138952 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq138707 eq113014
    | (have j0 := eq113014 X0
       grind)
    | exact resolve eq113014 eq138707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113014
  have eq163573 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq138952 X0
       have i₂ := eq113124 (M.op sF4 sF2)
       grind)
    | exact superpose eq113124 eq138952
    | (have j0 := eq138952 X0
       have j1 := eq113124 X0
       grind)
    | exact resolve eq138952 eq113124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113124 eq138952
  have eq163639 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq138709 eq163573
    | (have j0 := eq163573 X0 X0
       grind)
    | exact resolve eq163573 eq138709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163573
  have eq163640 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq163639 X1 X1
       grind)
    | (have r₁ := eq163639 X0 X1
       have r₂ := eq27
       grind)
    | exact resolve eq163639 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163639
  have eq163836 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq163640 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163640
  have eq163837 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq163836 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163836
  have eq164064 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq163837 y
       grind)
    | exact superpose eq163837 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq163837 y
       grind)
    | exact resolve eq13 eq163837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164141 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq387 y X0
       have i₂ := eq163837 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq163837 eq387
    | exact resolve eq387 eq163837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq164230 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq164064 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164064
  have eq164276 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq164141 X0
       have i₂ := eq163837 y
       grind)
    | exact superpose eq163837 eq164141
    | exact resolve eq164141 eq163837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164141
  have eq164378 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq164276 X0
       have i₂ := eq163837 X0
       grind)
    | exact superpose eq163837 eq164276
    | exact resolve eq164276 eq163837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164276
  have eq164574 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq708 y
       have i₂ := eq164230 y
       grind)
    | exact superpose eq164230 eq708
    | (have j0 := eq708 y
       grind)
    | exact resolve eq708 eq164230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq164230
  have eq164700 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq164574
  have eq164810 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq164700
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq164700
    | exact resolve eq164700 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq164700
  have eq164992 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq138707 eq164810
    | exact resolve eq164810 eq138707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138707 eq164810
  have eq167941 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op y X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq984 X0 x x X3
       have i₂ := eq164378 (M.op (M.op y (M.op (M.op sF0 (M.op x x)) x)) X0)
       grind)
    | exact superpose eq164378 eq984
    | exact resolve eq984 eq164378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984 eq164378
  have eq167942 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq167941 X0 X3
       have i₂ := eq163837 X3
       grind)
    | exact superpose eq163837 eq167941
    | exact resolve eq167941 eq163837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163837 eq167941
  have eq167950 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq164992 eq386
    | exact resolve eq386 eq164992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq164992
  have eq174537 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq167950 x
       have i₂ := eq167942 sF1 x
       grind)
    | exact superpose eq167942 eq167950
    | exact resolve eq167950 eq167942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167950
  have eq174640 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq174537 eq167942
    | exact resolve eq167942 eq174537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167942 eq174537
  have eq175411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq174640 eq138709
    | exact resolve eq138709 eq174640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138709 eq174640
  have eq175482 : False := by grind
  exact eq175482

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxx_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq52
    | exact resolve eq52 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq74 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq192 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
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
  have eq358 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq190 x y
       grind)
    | exact superpose eq190 eq16
    | (have j1 := eq190 x y
       grind)
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq190 X0 X0
       grind)
    | exact superpose eq190 eq68
    | (have j1 := eq190 X0 X0
       grind)
    | exact resolve eq68 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq190 X0 X0
       grind)
    | exact superpose eq190 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq190 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq190 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq190 X0 X1
       grind)
    | exact resolve eq12 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq379 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq374 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq380 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq373 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq384 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq379 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq379 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq379 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq425 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq384 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq384
    | (have j0 := eq384 (τ X0) X1
       grind)
    | exact resolve eq384 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq384
  have eq435 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq425
    | (have j0 := eq425 X0 X1
       grind)
    | exact resolve eq425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq442 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq435 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq435
    | (have j0 := eq435 X0 X1
       grind)
    | exact resolve eq435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq645 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1578 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq380 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq380
    | exact resolve eq380 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq1620 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1578 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1578
    | (have j0 := eq1578 X0
       grind)
    | exact resolve eq1578 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1630 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1620 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1620
    | (have j0 := eq1620 X0
       grind)
    | exact resolve eq1620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620
  have eq5037 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq192 (k (τ X0) (τ X0)) X0
       have i₂ := eq1630 (τ X0)
       grind)
    | exact superpose eq1630 eq192
    | (have j0 := eq192 (k (τ X0) (τ X0)) X0
       have j1 := eq1630 (τ X0)
       grind)
    | exact resolve eq192 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq5054 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq5037 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5037
  have eq5062 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq5054 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq5054 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq5054 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5054
  have eq5110 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 (σ (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5062 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq5062
    | (have j0 := eq5062 X0
       grind)
    | exact resolve eq5062 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5062
  have eq5113 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5110 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5110
    | (have j0 := eq5110 X0
       grind)
    | exact resolve eq5110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5110
  have eq5115 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5113 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq5113
    | (have j0 := eq5113 X0
       grind)
    | exact resolve eq5113 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5113
  have eq5116 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5115 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5115
    | (have j0 := eq5115 (σ X0)
       grind)
    | exact resolve eq5115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5115
  have eq5208 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5116 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq5116
    | (have j0 := eq5116 X0
       grind)
    | exact resolve eq5116 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5116
  have eq5211 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5208 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5208
    | (have j0 := eq5208 X0
       grind)
    | exact resolve eq5208 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5208
  have eq5212 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5211 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq5211
    | (have j0 := eq5211 X0
       grind)
    | exact resolve eq5211 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5211
  have eq5213 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5212 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5212
    | (have j0 := eq5212 X0
       grind)
    | exact resolve eq5212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5212
  have eq5229 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq5213 X0
       grind)
    | exact superpose eq5213 eq10
    | (have j1 := eq5213 X0
       grind)
    | exact resolve eq10 eq5213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5213
  have eq5252 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5229 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5229
    | (have j0 := eq5229 X0
       grind)
    | exact resolve eq5229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5229
  have eq5444 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq358
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq358
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq358 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq5447 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq5444
  have eq5667 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq89 (τ X0) (τ X0)
       grind)
    | exact superpose eq89 eq85
    | (have j0 := eq85 X0
       grind)
    | exact resolve eq85 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq5867 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5667 x
       have i₂ := eq192 (τ x) x
       grind)
    | exact superpose eq192 eq5667
    | (have j0 := eq5667 X0
       have j1 := eq192 (τ X0) X0
       grind)
    | exact resolve eq5667 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq5667
  have eq5886 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq5867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5867
  have eq5898 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5886 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5886
    | (have j0 := eq5886 X0
       grind)
    | exact resolve eq5886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5886
  have eq5997 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq5898 (σ X0)
       grind)
    | exact superpose eq5898 eq23
    | (have j1 := eq5898 (σ X0)
       grind)
    | exact resolve eq23 eq5898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898
  have eq6013 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5997 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq5997
    | (have j0 := eq5997 X0
       grind)
    | exact resolve eq5997 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5997
  have eq6035 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6013 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6013
    | (have j0 := eq6013 X0
       grind)
    | exact resolve eq6013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6013
  have eq6047 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6035 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6035
    | (have j0 := eq6035 X0
       grind)
    | exact resolve eq6035 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6035
  have eq6073 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5252 X0
       have i₂ := eq6047 X0
       grind)
    | exact superpose eq6047 eq5252
    | (have j0 := eq5252 X0
       have j1 := eq6047 X0
       grind)
    | exact resolve eq5252 eq6047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5252 eq6047
  have eq6106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6073 X0
       have j1 := eq442 X0 X0
       grind)
    | (have r₁ := eq6073 X0
       have r₂ := eq442 X0 x
       grind)
    | exact resolve eq6073 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq6073
  have eq6126 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6106 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq6106 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq6106 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6106
  have eq6307 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6126 (σ X0)
       grind)
    | exact superpose eq6126 eq15
    | exact resolve eq15 eq6126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6311 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq6126 (τ X0)
       grind)
    | exact superpose eq6126 eq32
    | exact resolve eq32 eq6126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq6327 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6311 X0
       have i₂ := eq6126 X0
       grind)
    | exact superpose eq6126 eq6311
    | exact resolve eq6311 eq6126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6311
  have eq6331 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6307 X0
       have i₂ := eq6126 X0
       grind)
    | exact superpose eq6126 eq6307
    | exact resolve eq6307 eq6126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6126 eq6307
  have eq6383 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 (τ X0) X1
       have i₂ := eq6327 X0
       grind)
    | exact superpose eq6327 eq74
    | exact resolve eq74 eq6327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6327
  have eq6492 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq6331 X0
       grind)
    | exact superpose eq6331 eq68
    | exact resolve eq68 eq6331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6515 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq6331 X0
       grind)
    | exact superpose eq6331 eq9
    | exact resolve eq9 eq6331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7550 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6515 (σ X0) X1
       have i₂ := eq6331 X0
       grind)
    | exact superpose eq6331 eq6515
    | exact resolve eq6515 eq6331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6515
  have eq50404 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5447
       have i₂ := eq6331 y
       grind)
    | exact superpose eq6331 eq5447
    | exact resolve eq5447 eq6331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447
  have eq50405 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq50404
       have i₂ := eq6331 y
       grind)
    | exact superpose eq6331 eq50404
    | exact resolve eq50404 eq6331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6331 eq50404
  have eq50774 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq50405
       grind)
    | exact superpose eq50405 eq10
    | exact resolve eq10 eq50405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50405
  have eq50925 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq50774
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq50774
    | exact resolve eq50774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50774
  have eq50926 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq50925
  have eq50999 : (M.op y y) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq50926
       grind)
    | exact superpose eq50926 eq10
    | exact resolve eq10 eq50926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50926
  have eq51147 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50999
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq50999
    | exact resolve eq50999 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50999
  have eq51148 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq51147
  have eq51159 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq74 y X0
       have i₂ := eq51148
       grind)
    | exact superpose eq51148 eq74
    | exact resolve eq74 eq51148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq51347 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq645 y y x
       have i₂ := eq51148
       grind)
    | exact superpose eq51148 eq645
    | exact resolve eq645 eq51148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51148
  have eq51374 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq51347 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq51347
    | exact resolve eq51347 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq51347
  have eq57835 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq51159 X0
       have i₂ := eq51374 X0
       grind)
    | exact superpose eq51374 eq51159
    | exact resolve eq51159 eq51374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51159 eq51374
  have eq57973 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq57835 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57835
  have eq57995 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 y
       have i₂ := eq57973 X0
       grind)
    | exact superpose eq57973 eq68
    | (have j1 := eq57973 X0
       grind)
    | exact resolve eq68 eq57973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq58066 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6492 y
       have i₂ := eq57973 X0
       grind)
    | exact superpose eq57973 eq6492
    | (have j1 := eq57973 X0
       grind)
    | exact resolve eq6492 eq57973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6492 eq57973
  have eq62608 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq58066 X0
       grind)
    | exact superpose eq58066 eq16
    | (have j1 := eq58066 X0
       grind)
    | exact resolve eq16 eq58066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58066
  have eq62731 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62608 X0
       have i₂ := eq57995 X1
       grind)
    | exact superpose eq57995 eq62608
    | (have j0 := eq62608 X0
       have j1 := eq57995 X0
       grind)
    | exact resolve eq62608 eq57995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57995 eq62608
  have eq62732 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq62731 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62731
  have eq63084 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq62732 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62732
  have eq63085 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq63084 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63084
  have eq63244 : ∀ X0 : G, (M.op (M.op (M.op (τ y) X0) (τ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6383 y X0
       have i₂ := eq63085 y
       grind)
    | exact superpose eq63085 eq6383
    | exact resolve eq6383 eq63085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6383
  have eq63403 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq645 y X1 X0
       have i₂ := eq63085 X0
       grind)
    | exact superpose eq63085 eq645
    | exact resolve eq645 eq63085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq63428 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq75 y X0
       have i₂ := eq63085 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq63085 eq75
    | exact resolve eq75 eq63085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq63604 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq63428 X0
       have i₂ := eq63085 y
       grind)
    | exact superpose eq63085 eq63428
    | exact resolve eq63428 eq63085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63428
  have eq63617 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63403 X0 X0
       have i₂ := eq63085 X0
       grind)
    | exact superpose eq63085 eq63403
    | exact resolve eq63403 eq63085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63403
  have eq63797 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq63604 X0
       have i₂ := eq63085 X0
       grind)
    | exact superpose eq63085 eq63604
    | exact resolve eq63604 eq63085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63085 eq63604
  have eq89573 : ∀ X0 : G, (M.op (τ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63244 X0
       have i₂ := eq63617 X0 (τ y)
       grind)
    | exact superpose eq63617 eq63244
    | exact resolve eq63244 eq63617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63244
  have eq89698 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ y))) X0) (σ (σ (τ y)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7550 (τ y) X0
       have i₂ := eq89573 (τ y)
       grind)
    | exact superpose eq89573 eq7550
    | exact resolve eq7550 eq89573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7550 eq89573
  have eq90099 : ∀ X0 : G, (M.op (σ (σ (τ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89698 X0
       have i₂ := eq63617 X0 (σ (σ (τ y)))
       grind)
    | exact superpose eq63617 eq89698
    | exact resolve eq89698 eq63617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89698
  have eq90216 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq90099 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq90099
    | exact resolve eq90099 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90099
  have eq90602 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq63617 X0 (σ y)
       have i₂ := eq90216 X0
       grind)
    | exact superpose eq90216 eq63617
    | exact resolve eq63617 eq90216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63617 eq90216
  have eq94562 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq90602 (σ x)
       grind)
    | exact superpose eq90602 eq16
    | exact resolve eq16 eq90602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90602
  have eq94696 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq94562
       have i₂ := eq63797 x
       grind)
    | exact superpose eq63797 eq94562
    | exact resolve eq94562 eq63797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63797 eq94562
  have eq94697 : False := by grind
  exact eq94697

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq45
    | (have j1 := eq90 x y
       grind)
    | exact resolve eq45 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq202 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq403 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4)) X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X0 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4 X5
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4)) X5) X0) X5) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 X0 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4 X5
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4)) X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4 X5
       have i₂ := eq56 X2 X1 X3 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq600 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq94 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq114 eq90
    | (have j0 := eq90 (σ x) (σ y)
       grind)
    | exact resolve eq90 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq703
    | exact resolve eq703 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq707 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq704
       have r₂ := eq28
       grind)
    | exact resolve eq704 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq716 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq707 eq421
    | exact resolve eq421 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq707
  have eq719 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq716
    | exact resolve eq716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq727 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq421 y
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq421
    | exact resolve eq421 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : x = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq719
  have eq730 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq727
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq727
    | exact resolve eq727 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq742 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq730 eq55
    | exact resolve eq55 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq745 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq730 eq28
    | exact resolve eq28 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq728
       grind)
    | exact superpose eq728 eq45
    | exact resolve eq45 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq766 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq764
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq764
    | exact resolve eq764 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq829 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq742
    | (have j0 := eq742 (σ y)
       grind)
    | exact resolve eq742 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq866 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq717 eq114
    | exact resolve eq114 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq867 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq717 eq60
    | exact resolve eq60 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq869 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq866
  have eq871 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq867
    | exact resolve eq867 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq881 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq421 y
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq421
    | exact resolve eq421 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq884 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq881
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq881
    | exact resolve eq881 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq894 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq884 eq27
    | exact resolve eq27 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq884 eq30
    | exact resolve eq30 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq927 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq895
    | exact resolve eq895 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq929 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq927 eq29
    | exact resolve eq29 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq958 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq929
    | exact resolve eq929 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq929
  have eq959 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq958 eq21
    | exact resolve eq21 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq959
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq959
    | exact resolve eq959 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq999 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq985 eq27
    | exact resolve eq27 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : (k x y) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq985 eq60
    | exact resolve eq60 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1020 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq985 eq766
    | exact resolve eq766 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq985
  have eq1024 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1020
  have eq1027 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1024
       have r₂ := eq28
       grind)
    | exact resolve eq1024 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1032 : (k x y) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq64 eq1004
    | exact resolve eq1004 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1050 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq894 eq421
    | exact resolve eq421 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1078 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq730 eq1050
    | exact resolve eq1050 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq1050
  have eq1086 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1078
  have eq1088 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq884 eq1086
    | exact resolve eq1086 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884 eq1086
  have eq1097 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1088
  have eq1118 : (τ (σ x)) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1027 eq64
    | exact resolve eq64 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1121 : x = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1118
    | exact resolve eq1118 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1123 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1097 eq894
    | exact resolve eq894 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq1097
  have eq1144 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1123
  have eq1158 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1144 eq829
    | exact resolve eq829 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1161 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1158
  have eq1164 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq1161
    | exact resolve eq1161 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq1165 : x = (k x y) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq958 eq1121
    | exact resolve eq1121 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq1121
  have eq1169 : x = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1165
  have eq1175 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1164 eq829
    | exact resolve eq829 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq1164
  have eq1183 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1175
  have eq1189 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq1169
       grind)
    | exact superpose eq1169 eq45
    | exact resolve eq45 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1193 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1189
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1189
    | exact resolve eq1189 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1208 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1183 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1183
       grind)
    | exact resolve eq13 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1209 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq1208 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1240 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90 x y
       have i₂ := eq871
       grind)
    | exact superpose eq871 eq90
    | (have j0 := eq90 x y
       grind)
    | exact resolve eq90 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq1241 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq1240
  have eq1243 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1241
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1241
    | exact resolve eq1241 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1255 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq421 y
       have i₂ := eq1243
       grind)
    | exact superpose eq1243 eq421
    | exact resolve eq421 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1258 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1255
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1255
    | exact resolve eq1255 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1279 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1258 eq745
    | exact resolve eq745 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq1258
  have eq1295 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1279
  have eq4527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1209 eq114
    | exact resolve eq114 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1209
  have eq4578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq4527
    | exact resolve eq4527 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4527
  have eq4587 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4578
       have r₂ := eq28
       grind)
    | exact resolve eq4578 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq4678 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq421 y
       have i₂ := eq4587
       grind)
    | exact superpose eq4587 eq421
    | exact resolve eq421 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq4689 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4678
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4678
    | exact resolve eq4678 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4678
  have eq4690 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4689
  have eq4752 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4690 eq1295
    | (have r₁ := eq1295
       have r₂ := eq4690
       grind)
    | exact resolve eq1295 eq4690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295 eq4690
  have eq4783 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4752
  have eq4784 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4783
  have eq4800 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4784 eq21
    | exact resolve eq21 eq4784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4801 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4784 eq46
    | exact resolve eq46 eq4784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq4828 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq4784
  have eq4841 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4801
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq4801
    | exact resolve eq4801 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4801
  have eq4842 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4800
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4800
    | exact resolve eq4800 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4800
  have eq5079 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x X0) (M.op x y)) X0) X1) = (M.op X0 (M.op (M.op (M.op (M.op x X0) (M.op x y)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq476 X0 X0 (M.op (M.op (M.op (M.op x X0) sF0) X0) x)
       have i₂ := eq14 X0 (M.op (M.op (M.op x X0) sF0) X0) x
       grind)
    | exact superpose eq14 eq476
    | exact resolve eq476 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq5089 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq5079
    | exact resolve eq5079 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq5079
  have eq5669 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1193 eq4841
    | exact resolve eq4841 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq4841
  have eq5688 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq5669
  have eq5694 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5688
       have r₂ := eq4828
       grind)
    | exact resolve eq5688 eq4828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5688
  have eq5932 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5694 eq64
    | exact resolve eq64 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq5694
  have eq5934 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq5932
    | exact resolve eq5932 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5932
  have eq5940 : x = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1032 eq5934
    | exact resolve eq5934 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032 eq5934
  have eq5948 : x = (k x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq5940
  have eq5952 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5948
       have r₂ := eq4828
       grind)
    | exact resolve eq5948 eq4828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5948
  have eq5956 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq5952
       grind)
    | exact superpose eq5952 eq45
    | exact resolve eq45 eq5952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq5952
  have eq5964 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5956
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5956
    | exact resolve eq5956 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5956
  have eq6240 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5964 eq90
    | (have j0 := eq90 (σ x) (σ y)
       grind)
    | exact resolve eq90 eq5964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq5964
  have eq6250 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq6240
    | exact resolve eq6240 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6240
  have eq14084 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq999 eq5089
    | (have j0 := eq5089 (σ x) (σ y)
       grind)
    | exact resolve eq5089 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq14258 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14084
       have r₂ := eq4828
       grind)
    | exact resolve eq14084 eq4828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828 eq14084
  have eq14418 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6250 eq421
    | exact resolve eq421 eq6250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq6250
  have eq14460 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14418
    | exact resolve eq14418 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14418
  have eq14462 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14460 eq28
    | exact resolve eq28 eq14460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14460
  have eq14519 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14462
       have r₂ := eq4842
       grind)
    | exact resolve eq14462 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14462
  have eq14525 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14519 eq202
    | exact resolve eq202 eq14519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq14560 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14519 eq14258
    | exact resolve eq14258 eq14519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14258 eq14519
  have eq14561 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq14560
  have eq14669 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14561 eq14525
    | exact resolve eq14525 eq14561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14525 eq14561
  have eq14717 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14669
  have eq14721 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14717
    | exact resolve eq14717 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14717
  have eq14726 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14721 eq28
    | exact resolve eq28 eq14721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14721
  have eq14786 : x = (M.op x y) := by
    first
    | (have r₁ := eq14726
       have r₂ := eq4842
       grind)
    | exact resolve eq14726 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4842 eq14726
  have eq14790 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq14786 eq21
    | exact resolve eq21 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq14792 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) := by
    intro X0
    first
    | exact superpose eq14786 eq51
    | exact resolve eq51 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq14839 : ∀ X0 : G, y = (M.op (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq14792 X0
       have i₂ := eq5089 x X0
       grind)
    | exact superpose eq5089 eq14792
    | exact resolve eq14792 eq5089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14792
  have eq14841 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14790
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14790
    | exact resolve eq14790 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14790
  have eq14842 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq14841 eq27
    | exact resolve eq27 eq14841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq15073 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq14839 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14839
    | (have j0 := eq14839 y
       grind)
    | exact resolve eq14839 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15083 : ∀ X3 : G, x = (M.op (M.op x (M.op (M.op x y) X3)) x) := by
    intro X3
    first
    | (have i₁ := eq403 x x x x y X3
       have i₂ := eq14839 (M.op (M.op (M.op x x) (M.op x x)) x)
       grind)
    | exact superpose eq14839 eq403
    | exact resolve eq403 eq14839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq15088 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq485 x x x x x y
       have i₂ := eq14839 (M.op (M.op (M.op (M.op (M.op x x) (M.op x x)) x) x) x)
       grind)
    | exact superpose eq14839 eq485
    | exact resolve eq485 eq14839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq14839
  have eq15124 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq15088
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15088
    | exact resolve eq15088 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15088
  have eq15127 : ∀ X3 : G, x = (M.op (M.op x (M.op (M.op x y) X3)) x) := by
    intro X3
    first
    | (have i₁ := eq15083 X3
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15083
    | (have j0 := eq15083 X3
       grind)
    | exact resolve eq15083 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15083
  have eq15131 : y = (M.op x y) := by
    first
    | exact superpose eq14786 eq15073
    | exact resolve eq15073 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15073
  have eq15132 : x = (M.op x x) := by
    first
    | exact superpose eq14786 eq15124
    | exact resolve eq15124 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15124
  have eq15135 : ∀ X3 : G, x = (M.op (M.op x (M.op x X3)) x) := by
    intro X3
    first
    | exact superpose eq14786 eq15127
    | exact resolve eq15127 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15127
  have eq15139 : y = (M.op x y) := by
    first
    | (have i₁ := eq15131
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15131
    | exact resolve eq15131 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15131
  have eq15140 : ∀ X3 : G, x = (M.op (M.op x X3) x) := by
    intro X3
    first
    | (have i₁ := eq15135 X3
       have i₂ := eq5089 x X3
       grind)
    | exact superpose eq5089 eq15135
    | exact resolve eq15135 eq5089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5089 eq15135
  have eq15141 : x = y := by
    first
    | exact superpose eq14786 eq15139
    | exact resolve eq15139 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14786 eq15139
  have eq15143 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15141
       grind)
    | exact superpose eq15141 eq25
    | exact resolve eq25 eq15141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15141
  have eq15218 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15143
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15143
    | exact resolve eq15143 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15143
  have eq15239 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14841 eq15218
    | exact resolve eq15218 eq14841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15218
  have eq15319 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15239 eq14842
    | exact resolve eq14842 eq15239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14842 eq15239
  have eq15590 : ∀ X3 : G, (M.op (M.op (M.op (M.op x x) X3) x) X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq455 x x x x x X3
       have i₂ := eq15140 (M.op (M.op (M.op x x) (M.op x x)) x)
       grind)
    | exact superpose eq15140 eq455
    | exact resolve eq455 eq15140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq15633 : ∀ X3 : G, (M.op (M.op (M.op x X3) x) X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq15590 X3
       have i₂ := eq15132
       grind)
    | exact superpose eq15132 eq15590
    | exact resolve eq15590 eq15132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15132 eq15590
  have eq15636 : ∀ X3 : G, (M.op x X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq15633 X3
       have i₂ := eq15140 X3
       grind)
    | exact superpose eq15140 eq15633
    | exact resolve eq15633 eq15140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15633
  have eq15654 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq15140 X0
       have i₂ := eq15636 X0
       grind)
    | exact superpose eq15636 eq15140
    | exact resolve eq15140 eq15636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15140 eq15636
  have eq15822 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq15654 x
       grind)
    | exact superpose eq15654 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq15654 x
       grind)
    | exact resolve eq13 eq15654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16016 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq15822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15822
  have eq16132 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq16016 X0
       have i₂ := eq15654 X0
       grind)
    | exact superpose eq15654 eq16016
    | exact resolve eq16016 eq15654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15654 eq16016
  have eq16238 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq600 x
       have i₂ := eq16132 x
       grind)
    | exact superpose eq16132 eq600
    | (have j0 := eq600 x
       grind)
    | exact resolve eq600 eq16132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq16132
  have eq16266 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16238
  have eq16286 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16266
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16266
    | exact resolve eq16266 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16266
  have eq16313 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14841 eq16286
    | exact resolve eq16286 eq14841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14841 eq16286
  have eq16334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15319 eq16313
    | exact resolve eq16313 eq15319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15319 eq16313
  have eq16354 : False := by grind
  exact eq16354

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyy_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq52
    | exact resolve eq52 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq74 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq192 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
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
  have eq358 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq190 x y
       grind)
    | exact superpose eq190 eq16
    | (have j1 := eq190 x y
       grind)
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq190 X0 X0
       grind)
    | exact superpose eq190 eq68
    | (have j1 := eq190 X0 X0
       grind)
    | exact resolve eq68 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq190 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq377 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq380 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq373 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq395 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq377 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq377
    | (have j0 := eq377 (τ X0)
       grind)
    | exact resolve eq377 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq377
  have eq405 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq395 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq395
    | (have j0 := eq395 X0
       grind)
    | exact resolve eq395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq412 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq405 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq405
    | (have j0 := eq405 X0
       grind)
    | exact resolve eq405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq615 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1523 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq380 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq380
    | exact resolve eq380 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq1565 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1523 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1523
    | (have j0 := eq1523 X0
       grind)
    | exact resolve eq1523 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1575 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1565 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1565
    | (have j0 := eq1565 X0
       grind)
    | exact resolve eq1565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq5328 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq192 (k (τ X0) (τ X0)) X0
       have i₂ := eq1575 (τ X0)
       grind)
    | exact superpose eq1575 eq192
    | (have j0 := eq192 (k (τ X0) (τ X0)) X0
       have j1 := eq1575 (τ X0)
       grind)
    | exact resolve eq192 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq5345 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq5328 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5328
  have eq5353 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq5345 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq5345 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq5345 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5345
  have eq5402 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 (σ (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5353 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq5353
    | (have j0 := eq5353 X0
       grind)
    | exact resolve eq5353 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5353
  have eq5405 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5402 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5402
    | (have j0 := eq5402 X0
       grind)
    | exact resolve eq5402 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5402
  have eq5407 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5405 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq5405
    | (have j0 := eq5405 X0
       grind)
    | exact resolve eq5405 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5405
  have eq5408 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5407 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5407
    | (have j0 := eq5407 (σ X0)
       grind)
    | exact resolve eq5407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5407
  have eq5508 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5408 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq5408
    | (have j0 := eq5408 X0
       grind)
    | exact resolve eq5408 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408
  have eq5511 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5508 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5508
    | (have j0 := eq5508 X0
       grind)
    | exact resolve eq5508 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5508
  have eq5512 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5511 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq5511
    | (have j0 := eq5511 X0
       grind)
    | exact resolve eq5511 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5511
  have eq5513 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5512 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5512
    | (have j0 := eq5512 X0
       grind)
    | exact resolve eq5512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5512
  have eq5529 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq5513 X0
       grind)
    | exact superpose eq5513 eq10
    | (have j1 := eq5513 X0
       grind)
    | exact resolve eq10 eq5513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5513
  have eq5552 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5529 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5529
    | (have j0 := eq5529 X0
       grind)
    | exact resolve eq5529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5529
  have eq5748 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq358
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq358
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq358 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq5751 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq5748
  have eq5981 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq89 (τ X0) (τ X0)
       grind)
    | exact superpose eq89 eq85
    | (have j0 := eq85 X0
       grind)
    | exact resolve eq85 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq6189 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5981 x
       have i₂ := eq192 (τ x) x
       grind)
    | exact superpose eq192 eq5981
    | (have j0 := eq5981 X0
       have j1 := eq192 (τ X0) X0
       grind)
    | exact resolve eq5981 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq5981
  have eq6208 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq6189 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6189
  have eq6220 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6208 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6208
    | (have j0 := eq6208 X0
       grind)
    | exact resolve eq6208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6208
  have eq6709 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq6220 (σ X0)
       grind)
    | exact superpose eq6220 eq23
    | (have j1 := eq6220 (σ X0)
       grind)
    | exact resolve eq23 eq6220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6220
  have eq6725 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6709 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq6709
    | (have j0 := eq6709 X0
       grind)
    | exact resolve eq6709 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6709
  have eq6746 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6725 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6725
    | (have j0 := eq6725 X0
       grind)
    | exact resolve eq6725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6725
  have eq6758 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6746 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6746
    | (have j0 := eq6746 X0
       grind)
    | exact resolve eq6746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746
  have eq6777 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6758 X0
       have i₂ := eq5552 X0
       grind)
    | exact superpose eq5552 eq6758
    | (have j0 := eq6758 X0
       have j1 := eq5552 X0
       grind)
    | exact resolve eq6758 eq5552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5552 eq6758
  have eq6825 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6777 X0
       have j1 := eq412 X0
       grind)
    | (have r₁ := eq6777 X0
       have r₂ := eq412 X0
       grind)
    | exact resolve eq6777 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq6777
  have eq6843 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6825 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq6825 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq6825 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6825
  have eq6886 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6843 (σ X0)
       grind)
    | exact superpose eq6843 eq15
    | exact resolve eq15 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6890 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq6843 (τ X0)
       grind)
    | exact superpose eq6843 eq32
    | exact resolve eq32 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq6906 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6890 X0
       have i₂ := eq6843 X0
       grind)
    | exact superpose eq6843 eq6890
    | exact resolve eq6890 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6890
  have eq6910 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6886 X0
       have i₂ := eq6843 X0
       grind)
    | exact superpose eq6843 eq6886
    | exact resolve eq6886 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6843 eq6886
  have eq6968 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 (τ X0) X1
       have i₂ := eq6906 X0
       grind)
    | exact superpose eq6906 eq74
    | exact resolve eq74 eq6906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6906
  have eq7085 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq6910 X0
       grind)
    | exact superpose eq6910 eq68
    | exact resolve eq68 eq6910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7109 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq6910 X0
       grind)
    | exact superpose eq6910 eq9
    | exact resolve eq9 eq6910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8199 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7109 (σ X0) X1
       have i₂ := eq6910 X0
       grind)
    | exact superpose eq6910 eq7109
    | exact resolve eq7109 eq6910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7109
  have eq37550 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5751
       have i₂ := eq6910 y
       grind)
    | exact superpose eq6910 eq5751
    | exact resolve eq5751 eq6910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5751
  have eq37551 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq37550
       have i₂ := eq6910 y
       grind)
    | exact superpose eq6910 eq37550
    | exact resolve eq37550 eq6910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6910 eq37550
  have eq38856 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq37551
       grind)
    | exact superpose eq37551 eq10
    | exact resolve eq10 eq37551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37551
  have eq39001 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq38856
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq38856
    | exact resolve eq38856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38856
  have eq39002 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq39001
  have eq39077 : (M.op y y) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq39002
       grind)
    | exact superpose eq39002 eq10
    | exact resolve eq10 eq39002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39002
  have eq39220 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39077
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq39077
    | exact resolve eq39077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39077
  have eq39221 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq39220
  have eq39234 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq74 y X0
       have i₂ := eq39221
       grind)
    | exact superpose eq39221 eq74
    | exact resolve eq74 eq39221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq39409 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq615 y y x
       have i₂ := eq39221
       grind)
    | exact superpose eq39221 eq615
    | exact resolve eq615 eq39221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39221
  have eq39453 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq39409 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq39409
    | exact resolve eq39409 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq39409
  have eq45414 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq39234 X0
       have i₂ := eq39453 X0
       grind)
    | exact superpose eq39453 eq39234
    | exact resolve eq39234 eq39453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39234 eq39453
  have eq45585 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq45414 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45414
  have eq45607 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 y
       have i₂ := eq45585 X0
       grind)
    | exact superpose eq45585 eq68
    | (have j1 := eq45585 X0
       grind)
    | exact resolve eq68 eq45585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq45669 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7085 y
       have i₂ := eq45585 X0
       grind)
    | exact superpose eq45585 eq7085
    | (have j1 := eq45585 X0
       grind)
    | exact resolve eq7085 eq45585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7085 eq45585
  have eq50047 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq45669 X0
       grind)
    | exact superpose eq45669 eq16
    | (have j1 := eq45669 X0
       grind)
    | exact resolve eq16 eq45669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45669
  have eq50187 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50047 X0
       have i₂ := eq45607 X1
       grind)
    | exact superpose eq45607 eq50047
    | (have j0 := eq50047 X0
       have j1 := eq45607 X0
       grind)
    | exact resolve eq50047 eq45607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45607 eq50047
  have eq50188 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50187 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50187
  have eq50576 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq50188 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50188
  have eq50577 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq50576 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50576
  have eq50717 : ∀ X0 : G, (M.op (M.op (M.op (τ y) X0) (τ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6968 y X0
       have i₂ := eq50577 y
       grind)
    | exact superpose eq50577 eq6968
    | exact resolve eq6968 eq50577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6968
  have eq50867 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq615 y X1 X0
       have i₂ := eq50577 X0
       grind)
    | exact superpose eq50577 eq615
    | exact resolve eq615 eq50577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq50919 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq75 y X0
       have i₂ := eq50577 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq50577 eq75
    | exact resolve eq75 eq50577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq51126 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq50919 X0
       have i₂ := eq50577 y
       grind)
    | exact superpose eq50577 eq50919
    | exact resolve eq50919 eq50577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50919
  have eq51155 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50867 X0 X0
       have i₂ := eq50577 X0
       grind)
    | exact superpose eq50577 eq50867
    | exact resolve eq50867 eq50577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50867
  have eq51325 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq51126 X0
       have i₂ := eq50577 X0
       grind)
    | exact superpose eq50577 eq51126
    | exact resolve eq51126 eq50577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50577 eq51126
  have eq61035 : ∀ X0 : G, (M.op (τ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50717 X0
       have i₂ := eq51155 X0 (τ y)
       grind)
    | exact superpose eq51155 eq50717
    | exact resolve eq50717 eq51155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50717
  have eq61158 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ y))) X0) (σ (σ (τ y)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8199 (τ y) X0
       have i₂ := eq61035 (τ y)
       grind)
    | exact superpose eq61035 eq8199
    | exact resolve eq8199 eq61035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8199 eq61035
  have eq61569 : ∀ X0 : G, (M.op (σ (σ (τ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61158 X0
       have i₂ := eq51155 X0 (σ (σ (τ y)))
       grind)
    | exact superpose eq51155 eq61158
    | exact resolve eq61158 eq51155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61158
  have eq61670 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61569 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq61569
    | exact resolve eq61569 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61569
  have eq62065 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq51155 X0 (σ y)
       have i₂ := eq61670 X0
       grind)
    | exact superpose eq61670 eq51155
    | exact resolve eq51155 eq61670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51155 eq61670
  have eq66063 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62065 (σ x)
       grind)
    | exact superpose eq62065 eq16
    | exact resolve eq16 eq62065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62065
  have eq66193 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq66063
       have i₂ := eq51325 x
       grind)
    | exact superpose eq51325 eq66063
    | exact resolve eq66063 eq51325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51325 eq66063
  have eq66194 : False := by grind
  exact eq66194

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_x_y_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq22 eq92
    | exact resolve eq92 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq110 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39
    | (have j0 := eq39 x
       grind)
    | exact resolve eq39 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq177 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq52
    | (have j0 := eq52 y
       grind)
    | exact resolve eq52 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq182 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq28 eq53
    | (have j0 := eq53 (σ y)
       grind)
    | exact resolve eq53 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq248 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq295 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq40
  have eq315 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq295 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq295
    | (have j0 := eq295 X0
       grind)
    | exact resolve eq295 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq374 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq374 (M.op X0 X1)
       grind)
    | exact superpose eq374 eq54
    | exact resolve eq54 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq380 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq374 X0
       grind)
    | exact superpose eq374 eq14
    | exact resolve eq14 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq400 : y = (M.op (M.op y (M.op x y)) y) := by
    first
    | (have i₁ := eq377 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq377
    | (have j0 := eq377 x y
       grind)
    | exact resolve eq377 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq452 : ∀ X0 : G, y = (M.op (M.op y (M.op (M.op y (M.op x y)) X0)) y) := by
    intro X0
    first
    | exact superpose eq400 eq14
    | exact resolve eq14 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq775 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq380
    | exact resolve eq380 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq55 eq380
    | exact resolve eq380 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56 eq380
    | exact resolve eq380 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq4206 : (σ x) = (k (σ (M.op x x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq315
    | exact resolve eq315 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq4258 : (σ x) = (σ (k (M.op x x) x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq41 eq4206
    | exact resolve eq4206 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4206
  have eq4993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq4993
    | exact resolve eq4993 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4993
  have eq5005 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq4994
       have r₂ := eq29
       grind)
    | exact resolve eq4994 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994
  have eq5035 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq5005
  have eq5036 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq5035
  have eq5417 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq5036 eq80
    | exact resolve eq80 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq5418 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq5036 eq93
    | exact resolve eq93 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq5036
  have eq5427 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5418
  have eq5436 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq5417
    | exact resolve eq5417 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5417
  have eq5465 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq775 x x
       have i₂ := eq5427
       grind)
    | exact superpose eq5427 eq775
    | exact resolve eq775 eq5427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5427
  have eq5471 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5465
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq5465
    | exact resolve eq5465 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465
  have eq5474 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq5471 eq31
    | exact resolve eq31 eq5471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5471
  have eq5575 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq5474
    | exact resolve eq5474 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5474
  have eq5576 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq5575
  have eq5766 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq5576 eq30
    | exact resolve eq30 eq5576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5576
  have eq5870 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq5766
    | exact resolve eq5766 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5766
  have eq5895 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq5870 eq22
    | exact resolve eq22 eq5870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5870
  have eq6003 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5895
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq5895
    | exact resolve eq5895 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5895
  have eq79481 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by grind
  clear eq5436
  have eq79533 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq79481
  have eq79551 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq79533
       grind)
    | exact superpose eq79533 eq71
    | exact resolve eq71 eq79533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq79533
  have eq79590 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq79551
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq79551
    | exact resolve eq79551 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79551
  have eq80056 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq79590 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq79590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79590
  have eq80065 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq80056
  have eq80087 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq80065
    | exact resolve eq80065 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80065
  have eq81772 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq80087 eq775
    | exact resolve eq775 eq80087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80087
  have eq81792 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq81772
    | exact resolve eq81772 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81772
  have eq82207 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq81792 eq29
    | exact resolve eq29 eq81792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81792
  have eq82258 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq6003 eq82207
    | (have r₁ := eq82207
       have r₂ := eq6003
       grind)
    | exact resolve eq82207 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82207
  have eq82259 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq82258
  have eq82260 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq82259
  have eq82266 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq82260 eq182
    | exact resolve eq182 eq82260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq82291 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq82260 eq781
    | exact resolve eq781 eq82260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82260
  have eq119130 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq82291 eq82266
    | exact resolve eq82266 eq82291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82266 eq82291
  have eq119185 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq119130
  have eq119194 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq119185
    | exact resolve eq119185 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119185
  have eq119196 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq119194 eq29
    | exact resolve eq29 eq119194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119194
  have eq119279 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq119196
       have r₂ := eq6003
       grind)
    | exact resolve eq119196 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003 eq119196
  have eq119281 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq119279 eq30
    | exact resolve eq30 eq119279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119279
  have eq119708 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq119281
    | exact resolve eq119281 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119281
  have eq119709 : x = (M.op x y) ∨ x = y := by grind
  clear eq119708
  have eq120585 : y = (M.op (M.op x x) y) ∨ x = y := by
    first
    | exact superpose eq119709 eq177
    | exact resolve eq177 eq119709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq120624 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq119709 eq778
    | exact resolve eq778 eq119709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126001 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq120585
       have i₂ := eq120624
       grind)
    | exact superpose eq120624 eq120585
    | exact resolve eq120585 eq120624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120585 eq120624
  have eq126052 : y = (M.op x y) ∨ x = y := by grind
  clear eq126001
  have eq126065 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq126052
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq126052
    | exact resolve eq126052 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126052
  have eq126318 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq126065 eq119709
    | exact resolve eq119709 eq126065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119709 eq126065
  have eq126329 : x = y := by grind
  clear eq126318
  have eq127231 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq126329
       grind)
    | exact superpose eq126329 eq20
    | exact resolve eq20 eq126329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq127232 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq126329
       grind)
    | exact superpose eq126329 eq26
    | exact resolve eq26 eq126329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq127288 : ∀ X0 : G, x = (M.op (M.op x (M.op (M.op x (M.op x y)) X0)) x) := by
    intro X0
    first
    | (have i₁ := eq452 X0
       have i₂ := eq126329
       grind)
    | exact superpose eq126329 eq452
    | exact resolve eq452 eq126329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq126329
  have eq127434 : ∀ X0 : G, x = (M.op (M.op x (M.op (M.op x y) X0)) x) := by
    intro X0
    first
    | exact superpose eq778 eq127288
    | exact resolve eq127288 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq127288
  have eq127475 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq127232
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq127232
    | exact resolve eq127232 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127232
  have eq127512 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq127475 eq28
    | exact resolve eq28 eq127475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq127475
  have eq128717 : (σ x) = (σ (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4258
       have i₂ := eq127231
       grind)
    | exact superpose eq127231 eq4258
    | exact resolve eq4258 eq127231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4258
  have eq128805 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110 eq128717
    | exact resolve eq128717 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq128717
  have eq128893 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq133802 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128805 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq128805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128805
  have eq133823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127512 eq133802
    | exact resolve eq133802 eq127512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133802
  have eq133835 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq133823
       have r₂ := eq29
       grind)
    | exact resolve eq133823 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133823
  have eq151272 : (σ (M.op x y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq133835 eq56
    | exact resolve eq56 eq133835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq151320 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq133835 eq775
    | exact resolve eq775 eq133835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151335 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127512 eq151320
    | exact resolve eq151320 eq127512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127512 eq151320
  have eq151365 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq781 eq151272
    | exact resolve eq151272 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq151272
  have eq152112 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq151335 eq151365
    | exact resolve eq151365 eq151335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151335 eq151365
  have eq152163 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq152112
  have eq152672 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq152163 eq133835
    | exact resolve eq133835 eq152163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133835 eq152163
  have eq152738 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq152672
  have eq152749 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq152738 eq30
    | exact resolve eq30 eq152738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq152738
  have eq153093 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq152749
    | exact resolve eq152749 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq152749
  have eq153094 : x = (M.op x y) := by grind
  clear eq153093
  have eq153179 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq153094 eq22
    | exact resolve eq22 eq153094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq153182 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq153094 eq55
    | exact resolve eq55 eq153094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq153451 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq153094 eq127434
    | exact resolve eq127434 eq153094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127434
  have eq153565 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq153451 X0
       have i₂ := eq775 x X0
       grind)
    | exact superpose eq775 eq153451
    | exact resolve eq153451 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq153451
  have eq153701 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq153179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq153179
    | exact resolve eq153179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153179
  have eq154143 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153701 eq128893
    | exact resolve eq128893 eq153701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128893
  have eq154156 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq154143
       have r₂ := eq29
       grind)
    | exact resolve eq154143 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154143
  have eq157146 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq153182 X0
       have i₂ := eq153565 X0
       grind)
    | exact superpose eq153565 eq153182
    | exact resolve eq153182 eq153565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153182 eq153565
  have eq158160 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq248 x X0
       have i₂ := eq157146 (τ X0)
       grind)
    | exact superpose eq157146 eq248
    | (have j0 := eq248 x X0
       grind)
    | exact resolve eq248 eq157146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq157146
  have eq158179 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq158160 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq158160
    | (have j0 := eq158160 X0
       grind)
    | exact resolve eq158160 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158160
  have eq158288 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq153701 eq158179
    | (have j0 := eq158179 X0
       grind)
    | exact resolve eq158179 eq153701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158179
  have eq158338 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq158288 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq158288
    | (have j0 := eq158288 X0
       grind)
    | exact resolve eq158288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158288
  have eq158366 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq158338 X0
       have i₂ := eq127231
       grind)
    | exact superpose eq127231 eq158338
    | (have j0 := eq158338 X0
       grind)
    | exact resolve eq158338 eq127231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127231 eq158338
  have eq158384 : ∀ X0 : G, (τ X0) = x ∨ (k X0 (σ (M.op x y))) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq153094 eq158366
    | (have j0 := eq158366 X0
       grind)
    | exact resolve eq158366 eq153094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153094 eq158366
  have eq158385 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | (have j0 := eq158384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158384
  have eq174362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq158385 eq154156
    | (have j1 := eq158385 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq154156 eq158385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154156 eq158385
  have eq174369 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq174362
       have r₂ := eq29
       grind)
    | exact resolve eq174362 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174362
  have eq174962 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq174369 eq15
    | exact resolve eq15 eq174369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174369
  have eq175328 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq174962
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq174962
    | exact resolve eq174962 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq174962
  have eq175446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153701 eq175328
    | exact resolve eq175328 eq153701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153701 eq175328
  have eq175545 : False := by grind
  exact eq175545
