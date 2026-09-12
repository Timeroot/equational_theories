import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq83
    | exact resolve eq83 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq91
    | exact resolve eq91 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq115 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq436 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  clear eq54
  have eq444 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq436 X0
       grind)
    | exact superpose eq436 eq14
    | exact resolve eq14 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq971 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq444 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq444
    | exact resolve eq444 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq5925 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq687 X0
       grind)
    | (have r₁ := eq687 x
       have r₂ := eq971 x x
       grind)
    | exact resolve eq687 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq25537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq25537
    | exact resolve eq25537 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25537
  have eq25555 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq25544
       have r₂ := eq29
       grind)
    | exact resolve eq25544 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25544
  have eq25586 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25555 eq5925
    | exact resolve eq5925 eq25555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25620 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25555 eq971
    | exact resolve eq971 eq25555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25555
  have eq25626 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq25620
    | exact resolve eq25620 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25620
  have eq25637 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25626 eq436
    | exact resolve eq436 eq25626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25626
  have eq25680 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq25637
    | exact resolve eq25637 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25637
  have eq25681 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq25680
  have eq25713 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5925 x
       have i₂ := eq25681
       grind)
    | exact superpose eq25681 eq5925
    | exact resolve eq5925 eq25681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5925 eq25681
  have eq26547 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq25713
       grind)
    | exact superpose eq25713 eq46
    | exact resolve eq46 eq25713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25713
  have eq26579 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq26547
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq26547
    | exact resolve eq26547 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26547
  have eq26820 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26579 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26579
  have eq26829 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq26820
    | exact resolve eq26820 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26820
  have eq26830 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq26829
  have eq33198 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26830 eq971
    | exact resolve eq971 eq26830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26830
  have eq33207 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq33198
    | exact resolve eq33198 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33198
  have eq33208 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq33207
  have eq33220 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33208 eq436
    | exact resolve eq436 eq33208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33208
  have eq33270 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq33220
    | exact resolve eq33220 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33220
  have eq33271 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33270
  have eq33283 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33271
  have eq33347 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33283
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq33283
    | exact resolve eq33283 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33283
  have eq33481 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq33347
       grind)
    | exact superpose eq33347 eq46
    | exact resolve eq46 eq33347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq33347
  have eq33526 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq33481
    | exact resolve eq33481 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33481
  have eq33623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33526 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq33526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33526
  have eq33638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq33623
    | exact resolve eq33623 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33623
  have eq33649 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33638
       have r₂ := eq29
       grind)
    | exact resolve eq33638 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33638
  have eq35709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33649 eq971
    | exact resolve eq971 eq33649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33649
  have eq35718 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq35709
    | exact resolve eq35709 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35709
  have eq35719 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq35718
  have eq35734 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35719 eq436
    | exact resolve eq436 eq35719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35719
  have eq35784 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq35734
    | exact resolve eq35734 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35734
  have eq35785 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq35784
  have eq35788 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq35785 eq29
    | exact resolve eq29 eq35785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq66391 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25586 eq92
    | exact resolve eq92 eq25586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25586
  have eq66415 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq66391
  have eq66424 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq66415
       have r₂ := eq35788
       grind)
    | exact resolve eq66415 eq35788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66415
  have eq66739 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq66424
  have eq66802 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq66739
    | exact resolve eq66739 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq66739
  have eq66809 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq35785 eq66802
    | exact resolve eq66802 eq35785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35785 eq66802
  have eq67144 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq66809 eq92
    | exact resolve eq92 eq66809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq66809
  have eq67167 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq67144
  have eq67175 : y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq67167
       have r₂ := eq35788
       grind)
    | exact resolve eq67167 eq35788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67167
  have eq67255 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq971 x x
       have i₂ := eq67175
       grind)
    | exact superpose eq67175 eq971
    | exact resolve eq971 eq67175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq67175
  have eq67275 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67255
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq67255
    | exact resolve eq67255 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67255
  have eq67294 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq436 y
       have i₂ := eq67275
       grind)
    | exact superpose eq67275 eq436
    | exact resolve eq436 eq67275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq67275
  have eq67349 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67294
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq67294
    | exact resolve eq67294 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq67294
  have eq67350 : y = (M.op x y) := by grind
  clear eq67349
  have eq67652 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq67350 eq22
    | exact resolve eq22 eq67350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq67350
  have eq67942 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq67652
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq67652
    | exact resolve eq67652 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq67652
  have eq67943 : False := by grind
  exact eq67943

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_y_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq25 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
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
  have eq33 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq35 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq23
    | exact resolve eq23 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq43 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq62 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq19
    | exact resolve eq19 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq98 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq106 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq65 (τ X0)
       grind)
    | exact superpose eq65 eq19
    | exact resolve eq19 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq109 : ∀ X0 : G, (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq106
    | exact resolve eq106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq136 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq98 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq98
    | exact resolve eq98 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq142 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq9
    | exact resolve eq9 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq142
    | exact resolve eq142 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq9
    | exact resolve eq9 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact superpose eq13 eq15
    | (have j1 := eq13 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 X2 X3 : G, (σ (k X2 (k (τ X3) (k X0 (τ X1))))) = (k (σ X2) (k X3 (k (σ X0) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X3 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq357 : ∀ X0 X1 X2 X3 : G, (σ (k (k (τ X2) (k X0 (τ X1))) X3)) = (k (k X2 (k (σ X0) X1)) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X2 (k X0 (τ X1)) X3
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq682 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq1117 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq238 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1337 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1117 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1117
    | exact resolve eq1117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq1117 X0
       grind)
    | exact superpose eq1117 eq43
    | (have j1 := eq1117 X0
       grind)
    | exact resolve eq43 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1344 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq136 (σ X0)
       have i₂ := eq1117 X0
       grind)
    | exact superpose eq1117 eq136
    | (have j1 := eq1117 X0
       grind)
    | exact resolve eq136 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1352 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (k X0 X0))) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq1117 X0
       grind)
    | exact superpose eq1117 eq9
    | (have j1 := eq1117 X0
       grind)
    | exact resolve eq9 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1371 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1380 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1340 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq1340
    | (have j0 := eq1340 X0
       grind)
    | exact resolve eq1340 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1383 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1337 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1337
    | (have j0 := eq1337 X0
       grind)
    | exact resolve eq1337 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1386 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1383 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1383
    | (have j0 := eq1383 X0
       grind)
    | exact resolve eq1383 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383
  have eq1439 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1371 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1371
    | exact resolve eq1371 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1443 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq1371 X0
       grind)
    | exact superpose eq1371 eq43
    | (have j1 := eq1371 X0
       grind)
    | exact resolve eq43 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1485 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1443 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1443
    | (have j0 := eq1443 X0
       grind)
    | exact resolve eq1443 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443
  have eq1488 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1439 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1439
    | (have j0 := eq1439 X0
       grind)
    | exact resolve eq1439 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1491 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1488 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1488
    | (have j0 := eq1488 X0
       grind)
    | exact resolve eq1488 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1506 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq1491 X0
       grind)
    | exact superpose eq1491 eq9
    | (have j1 := eq1491 X0
       grind)
    | exact resolve eq9 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1517 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq173 X0 X0 x
       have i₂ := eq1491 X0
       grind)
    | exact superpose eq1491 eq173
    | (have j1 := eq1491 X0
       grind)
    | exact resolve eq173 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1557 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq1491 (τ X0)
       grind)
    | exact superpose eq1491 eq33
    | (have j1 := eq1491 (τ X0)
       grind)
    | exact resolve eq33 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1491
  have eq1562 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1557 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1557
    | (have j0 := eq1557 X0
       grind)
    | exact resolve eq1557 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq1582 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1517 X0 X1
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq1517
    | (have j0 := eq1517 X0 X1
       grind)
    | exact resolve eq1517 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1592 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1562 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq1562
    | (have j0 := eq1562 X0
       grind)
    | exact resolve eq1562 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq1609 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1485 X0
       have i₂ := eq1386 X0
       grind)
    | exact superpose eq1386 eq1485
    | (have j1 := eq1386 X0
       grind)
    | exact resolve eq1485 eq1386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386 eq1485
  have eq1614 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609
  have eq1630 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1592 (σ X0)
       have i₂ := eq30 X0 (σ X0)
       grind)
    | exact superpose eq30 eq1592
    | (have j0 := eq1592 (σ X0)
       grind)
    | exact resolve eq1592 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq1638 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1630 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1630
    | (have j0 := eq1630 X0
       grind)
    | exact resolve eq1630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq1643 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1638 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1638
    | (have j0 := eq1638 X0
       grind)
    | exact resolve eq1638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq1677 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 X1
       have i₂ := eq682 X0 X1
       grind)
    | (have i₁ := eq238 X1 X0
       have i₂ := eq682 X0 X1
       grind)
    | exact superpose eq682 eq238
    | (have j0 := eq238 X1 X0
       have j1 := eq682 X0 X1
       grind)
    | (have r₁ := eq238 X0 X1
       have r₂ := eq682 X0 X1
       grind)
    | (have r₁ := eq238 X1 X0
       have r₂ := eq682 X0 X1
       grind)
    | exact resolve eq238 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq682
  have eq1699 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1677 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq1700 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1699 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699
  have eq2018 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X0) ≠ X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1506 X0 X1
       have i₂ := eq1582 X0 X1
       grind)
    | exact superpose eq1582 eq1506
    | (have j0 := eq1506 X0 X1
       have j1 := eq1582 X0 X1
       grind)
    | exact resolve eq1506 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2051 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X1) X2) = (M.op (M.op (M.op (M.op (M.op X1 X0) X1) X2) X0) (M.op (M.op (M.op X1 X0) X1) X2)) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173 (M.op (M.op X1 X0) X1) X2 X0
       have i₂ := eq1506 X1 X0
       grind)
    | exact superpose eq1506 eq173
    | (have j1 := eq1506 X1 X1
       grind)
    | exact resolve eq173 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq2059 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq2018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq2064 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) X0) (M.op X1 X2)) ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq1582 eq2051
    | (have j0 := eq2051 X0 X1 X2
       have j1 := eq1582 (M.op X1 X2) X0
       grind)
    | exact resolve eq2051 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582 eq2051
  have eq2100 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X2) = X2 ∨ (k X1 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq2059 eq2064
    | (have j0 := eq2064 X0 X1 X2
       have j1 := eq2059 (M.op X2 X0) X2
       grind)
    | exact resolve eq2064 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064
  have eq2206 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2059 (σ x) (σ y)
       grind)
    | exact superpose eq2059 eq16
    | (have j1 := eq2059 (σ x) x
       grind)
    | exact resolve eq16 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2228 : (σ x) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq2206
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2206
    | exact resolve eq2206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2489 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1700 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1700
    | exact resolve eq1700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2501 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1700 x y
       grind)
    | exact superpose eq1700 eq16
    | (have j1 := eq1700 x y
       grind)
    | exact resolve eq16 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq2563 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2489 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq2489
    | (have j0 := eq2489 X0 X1
       grind)
    | exact resolve eq2489 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2489
  have eq2824 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x ≠ (k x x) := by
    first
    | (have i₁ := eq2228
       have i₂ := eq1643 x
       grind)
    | exact superpose eq1643 eq2228
    | (have j1 := eq1643 x
       grind)
    | (have r₁ := eq2228
       have r₂ := eq1643 x
       grind)
    | exact resolve eq2228 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643 eq2228
  have eq2825 : (σ (M.op x y)) ≠ (σ y) ∨ x ≠ (k x x) := by grind
  clear eq2824
  have eq2827 : (σ y) ≠ (σ y) ∨ x ≠ (k x x) := by
    first
    | exact superpose eq2059 eq2825
    | (have j1 := eq2059 x x
       grind)
    | exact resolve eq2825 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059 eq2825
  have eq2828 : x ≠ (k x x) := by grind
  clear eq2827
  have eq2840 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2563 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2563
    | exact resolve eq2563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2857 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq2563 X0 X1
       grind)
    | exact superpose eq2563 eq30
    | (have j1 := eq2563 X0 X1
       grind)
    | exact resolve eq30 eq2563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2563
  have eq3114 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq1380 X0
       grind)
    | exact superpose eq1380 eq43
    | (have j1 := eq1380 X0
       grind)
    | exact resolve eq43 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3163 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3114 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3114
    | (have j0 := eq3114 X0
       grind)
    | exact resolve eq3114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq3181 : ∀ X0 : G, (τ X0) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3163 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq3163
    | exact resolve eq3163 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3200 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (k (τ (k (k X0 (σ X1)) (k X0 (σ X1)))) (k (τ X0) X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1 (k (k X0 (σ X1)) (k X0 (σ X1)))
       have i₂ := eq3163 (k X0 (σ X1))
       grind)
    | exact superpose eq3163 eq35
    | (have j1 := eq3163 (k X0 (σ X1))
       grind)
    | exact resolve eq35 eq3163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3208 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (k (k (τ (k X0 (σ X1))) (k (τ X0) X1)) (k (τ X0) X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3200 X0 X1
       have i₂ := eq35 X0 X1 (k X0 (σ X1))
       grind)
    | exact superpose eq35 eq3200
    | (have j0 := eq3200 X0 X1
       grind)
    | exact resolve eq3200 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3200
  have eq3223 : ∀ X0 : G, (τ X0) = (τ (k (k X0 X0) X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3181 X0
       have i₂ := eq34 X0 (k X0 X0)
       grind)
    | exact superpose eq34 eq3181
    | (have j0 := eq3181 X0
       grind)
    | exact resolve eq3181 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3181
  have eq3226 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (k (k (τ X0) X1) (k (τ X0) X1)) (k (τ X0) X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3208 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq3208
    | (have j0 := eq3208 X0 X1
       grind)
    | exact resolve eq3208 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3208
  have eq8448 : ∀ X0 : G, (k (k X0 X0) X0) = (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) (k (k X0 X0) X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq109 (k (k X0 X0) X0)
       have i₂ := eq3223 X0
       grind)
    | exact superpose eq3223 eq109
    | (have j1 := eq3223 X0
       grind)
    | exact resolve eq109 eq3223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3223
  have eq12374 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2501
       have i₂ := eq2840 y x
       grind)
    | exact superpose eq2840 eq2501
    | (have j1 := eq2840 (σ y) (σ x)
       grind)
    | exact resolve eq2501 eq2840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12378 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq12374
  have eq12393 : x = (k (k x x) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1380 x
       have i₂ := eq12378
       grind)
    | exact superpose eq12378 eq1380
    | (have j0 := eq1380 x
       grind)
    | exact resolve eq1380 eq12378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq12397 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq12378
       grind)
    | exact superpose eq12378 eq43
    | exact resolve eq43 eq12378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq12409 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  have eq12445 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq155 (σ x) (σ x)
       have i₂ := eq12378
       grind)
    | exact superpose eq12378 eq155
    | exact resolve eq155 eq12378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12378
  have eq12489 : (σ x) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12409
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12409
    | exact resolve eq12409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12409
  have eq12493 : y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12397
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq12397
    | exact resolve eq12397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12397
  have eq12509 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2840 eq12489
    | (have j1 := eq2840 y x
       grind)
    | exact resolve eq12489 eq2840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12489
  have eq12517 : x = (k y x) ∨ x = (k y x) := by grind
  clear eq12493
  have eq12584 : x = (k y x) := by grind
  clear eq12517
  have eq12590 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq2501
       have i₂ := eq12584
       grind)
    | exact superpose eq12584 eq2501
    | exact resolve eq2501 eq12584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501
  have eq12594 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2840 y x
       have i₂ := eq12584
       grind)
    | exact superpose eq12584 eq2840
    | (have j0 := eq2840 y x
       grind)
    | exact resolve eq2840 eq12584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12584
  have eq13037 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq155 x x
       have i₂ := eq12594
       grind)
    | exact superpose eq12594 eq155
    | exact resolve eq155 eq12594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12594
  have eq13179 : x = (M.op x y) ∨ x ≠ y := by grind
  clear eq13037
  have eq13204 : x = (M.op x x) ∨ x ≠ y := by
    first
    | (have i₁ := eq155 x y
       have i₂ := eq13179
       grind)
    | exact superpose eq13179 eq155
    | exact resolve eq155 eq13179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13179
  have eq13256 : x = (k x x) ∨ x ≠ y := by grind
  clear eq13204
  have eq13321 : x ≠ y := by
    first
    | (have r₁ := eq13256
       have r₂ := eq2828
       grind)
    | exact resolve eq13256 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13256
  have eq14487 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12445
       grind)
    | exact superpose eq12445 eq16
    | exact resolve eq16 eq12445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12445
  have eq14547 : y = (M.op x x) ∨ (σ x) ≠ (σ y) := by
    first
    | exact superpose eq12509 eq14487
    | exact resolve eq14487 eq12509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14487
  have eq14565 : (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq1614 x
       have i₂ := eq14547
       grind)
    | exact superpose eq14547 eq1614
    | exact resolve eq1614 eq14547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq14627 : (σ x) ≠ (σ y) ∨ x = y := by grind
  clear eq14565
  have eq14638 : (σ x) ≠ (σ y) := by
    first
    | (have r₁ := eq14627
       have r₂ := eq13321
       grind)
    | exact resolve eq14627 eq13321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14627
  have eq18926 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq2857 (σ x) x
       have i₂ := eq12590
       grind)
    | exact superpose eq12590 eq2857
    | exact resolve eq2857 eq12590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857 eq12590
  have eq19019 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have r₁ := eq18926
       have r₂ := eq14638
       grind)
    | exact resolve eq18926 eq14638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18926
  have eq19044 : (k x x) = (τ (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq19019
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19019
    | exact resolve eq19019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19019
  have eq19062 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19044
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq19044
    | exact resolve eq19044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19044
  have eq19074 : (σ x) ≠ (σ x) ∨ y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19062
       have i₂ := eq12509
       grind)
    | exact superpose eq12509 eq19062
    | (have r₁ := eq19062
       have r₂ := eq12509
       grind)
    | exact resolve eq19062 eq12509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19062
  have eq19075 : y = (k x x) ∨ y = (M.op x x) := by grind
  clear eq19074
  have eq19131 : y = (M.op x x) ∨ (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq19075
       grind)
    | exact superpose eq19075 eq13
    | (have j0 := eq13 x x
       grind)
    | exact resolve eq13 eq19075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19132 : y = (M.op x x) ∨ (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq19131
  have eq19133 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq19132
  have eq19200 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq155 x x
       have i₂ := eq19133
       grind)
    | exact superpose eq19133 eq155
    | exact resolve eq155 eq19133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19133
  have eq26265 : x = (M.op x (k x x)) ∨ (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2840 (k x x) x
       have i₂ := eq12393
       grind)
    | exact superpose eq12393 eq2840
    | (have j0 := eq2840 x x
       grind)
    | exact resolve eq2840 eq12393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12393
  have eq26272 : x = (M.op x (k x x)) ∨ (k x x) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq26265
       have r₂ := eq14547
       grind)
    | exact resolve eq26265 eq14547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26265
  have eq26276 : x = (M.op x (k x x)) ∨ (k x x) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq2840 eq26272
    | (have j1 := eq2840 x x
       grind)
    | exact resolve eq26272 eq2840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26272
  have eq26278 : x = (M.op x (k x x)) ∨ (k x x) = (M.op x x) := by
    first
    | (have r₁ := eq26276
       have r₂ := eq13321
       grind)
    | exact resolve eq26276 eq13321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26276
  have eq26314 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x (k x x)
       have i₂ := eq26278
       grind)
    | exact superpose eq26278 eq9
    | exact resolve eq9 eq26278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26335 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq173 x (k x x) x
       have i₂ := eq26278
       grind)
    | exact superpose eq26278 eq173
    | exact resolve eq173 eq26278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26387 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq26335 X0
       have i₂ := eq155 x X0
       grind)
    | exact superpose eq155 eq26335
    | exact resolve eq26335 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26335
  have eq26646 : ∀ X0 : G, (M.op x X0) = X0 ∨ (k x x) = (M.op x x) ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq26314 X0
       have i₂ := eq26387 X0
       grind)
    | exact superpose eq26387 eq26314
    | exact resolve eq26314 eq26387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26314 eq26387
  have eq26759 : ∀ X0 : G, (k x x) = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26646 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26646
  have eq26834 : ∀ X0 : G, (M.op x X0) = X0 ∨ x ≠ (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2828
       have i₂ := eq26759 X0
       grind)
    | exact superpose eq26759 eq2828
    | (have j1 := eq26759 X0
       grind)
    | exact resolve eq2828 eq26759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26841 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19075
       have i₂ := eq26759 X0
       grind)
    | exact superpose eq26759 eq19075
    | (have j1 := eq26759 X0
       grind)
    | exact resolve eq19075 eq26759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19075
  have eq26893 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26841 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26841
  have eq26946 : x = (k x x) ∨ (k x x) = (M.op x x) ∨ x ≠ (M.op x x) := by
    first
    | (have i₁ := eq26278
       have i₂ := eq26834 (k x x)
       grind)
    | exact superpose eq26834 eq26278
    | exact resolve eq26278 eq26834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26278
  have eq26951 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x ≠ (M.op x x) := by
    first
    | (have i₁ := eq12509
       have i₂ := eq26834 y
       grind)
    | exact superpose eq26834 eq12509
    | exact resolve eq12509 eq26834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12509 eq26834
  have eq27139 : y = (M.op x x) ∨ x ≠ (M.op x x) := by
    first
    | (have r₁ := eq26951
       have r₂ := eq14547
       grind)
    | exact resolve eq26951 eq14547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14547 eq26951
  have eq27141 : x = (k x x) ∨ (k x x) = (M.op x x) := by
    first
    | (have r₁ := eq26946
       have r₂ := eq26759 x
       grind)
    | exact resolve eq26946 eq26759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26759 eq26946
  have eq27163 : y = (M.op x x) := by
    first
    | (have r₁ := eq27139
       have r₂ := eq26893 x
       grind)
    | exact resolve eq27139 eq26893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26893 eq27139
  have eq27164 : (k x x) = (M.op x x) := by
    first
    | (have r₁ := eq27141
       have r₂ := eq2828
       grind)
    | exact resolve eq27141 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828 eq27141
  have eq27198 : x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19200
       have i₂ := eq27163
       grind)
    | exact superpose eq27163 eq19200
    | exact resolve eq19200 eq27163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19200
  have eq27610 : y = (k x x) := by
    first
    | (have i₁ := eq27164
       have i₂ := eq27163
       grind)
    | exact superpose eq27163 eq27164
    | exact resolve eq27164 eq27163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27164
  have eq27889 : y = (M.op x y) := by
    first
    | (have r₁ := eq27198
       have r₂ := eq13321
       grind)
    | exact resolve eq27198 eq13321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13321 eq27198
  have eq27919 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27889
       grind)
    | exact superpose eq27889 eq16
    | exact resolve eq16 eq27889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27889
  have eq31450 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1344 x
       have i₂ := eq27610
       grind)
    | exact superpose eq27610 eq1344
    | (have j0 := eq1344 x
       grind)
    | exact resolve eq1344 eq27610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq33671 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 X0) ≠ X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2100 (σ x) X0 (σ y)
       have i₂ := eq31450
       grind)
    | exact superpose eq31450 eq2100
    | (have j0 := eq2100 X0 X0 x
       grind)
    | exact resolve eq2100 eq31450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100 eq31450
  have eq33684 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq33671 X0
       grind)
    | (have r₁ := eq33671 X0
       have r₂ := eq27919
       grind)
    | exact resolve eq33671 eq27919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33671
  have eq33705 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    grind
  clear eq33684
  have eq33778 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq33705 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq33705
    | (have j0 := eq33705 X0
       grind)
    | exact resolve eq33705 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33705
  have eq33783 : ∀ X0 : G, (σ x) = (σ y) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq33778 X0
       have i₂ := eq27610
       grind)
    | exact superpose eq27610 eq33778
    | (have j0 := eq33778 X0
       grind)
    | exact resolve eq33778 eq27610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27610 eq33778
  have eq33785 : ∀ X0 : G, (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq33783 X0
       grind)
    | (have r₁ := eq33783 X0
       have r₂ := eq14638
       grind)
    | exact resolve eq33783 eq14638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14638 eq33783
  have eq33794 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33785 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq33785
    | exact resolve eq33785 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35713 : ∀ X0 X1 X2 : G, (σ (k X1 (k (τ X2) (τ X0)))) = (k (σ X1) (k X2 (k (σ (k (τ X0) (τ X0))) X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319 (k (τ X0) (τ X0)) X0 X1 X2
       have i₂ := eq3163 (τ X0)
       grind)
    | exact superpose eq3163 eq319
    | (have j1 := eq3163 (τ X0)
       grind)
    | exact resolve eq319 eq3163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq35885 : ∀ X0 X1 X2 : G, (σ (k X1 (k (τ X2) (τ X0)))) = (k (σ X1) (k X2 (k (σ (k (τ X0) (τ X0))) X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq35713 X0 X1 X2
       grind)
    | (have r₁ := eq35713 X0 X1 X2
       have r₂ := eq33785 (τ X0)
       grind)
    | exact resolve eq35713 eq33785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35713
  have eq35942 : ∀ X0 X1 X2 : G, (σ (k X1 (k (τ X2) (τ X0)))) = (k (σ X1) (k X2 (k (k (σ (τ X0)) X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35885 X0 X1 X2
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq35885
    | exact resolve eq35885 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35885
  have eq35967 : ∀ X0 X1 X2 : G, (σ (k X1 (k (τ X2) (τ X0)))) = (k (σ X1) (k X2 (k (k X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35942 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35942
    | exact resolve eq35942 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35942
  have eq35978 : ∀ X0 X1 X2 : G, (σ (k X1 (τ (k X2 X0)))) = (k (σ X1) (k X2 (k (k X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35967 X0 X1 X2
       have i₂ := eq34 X0 X2
       grind)
    | exact superpose eq34 eq35967
    | exact resolve eq35967 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35967
  have eq35987 : ∀ X0 X1 X2 : G, (k (σ X1) (k X2 X0)) = (k (σ X1) (k X2 (k (k X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35978 X0 X1 X2
       have i₂ := eq19 (k X2 X0) X1
       grind)
    | exact superpose eq19 eq35978
    | exact resolve eq35978 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35978
  have eq37966 : ∀ X0 X1 X2 : G, (σ (k (k (τ X1) (τ X0)) X2)) = (k (k X1 (k (σ (k (τ X0) (τ X0))) X0)) (σ X2)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq357 (k (τ X0) (τ X0)) X0 X1 X2
       have i₂ := eq3163 (τ X0)
       grind)
    | exact superpose eq3163 eq357
    | (have j1 := eq3163 (τ X0)
       grind)
    | exact resolve eq357 eq3163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq38119 : ∀ X0 X1 X2 : G, (σ (k (k (τ X1) (τ X0)) X2)) = (k (k X1 (k (σ (k (τ X0) (τ X0))) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37966 X0 X1 X2
       grind)
    | (have r₁ := eq37966 X0 X1 X2
       have r₂ := eq33785 (τ X0)
       grind)
    | exact resolve eq37966 eq33785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37966
  have eq38168 : ∀ X0 X1 X2 : G, (σ (k (k (τ X1) (τ X0)) X2)) = (k (k X1 (k (k (σ (τ X0)) X0) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38119 X0 X1 X2
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq38119
    | exact resolve eq38119 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq38119
  have eq38189 : ∀ X0 X1 X2 : G, (σ (k (k (τ X1) (τ X0)) X2)) = (k (k X1 (k (k X0 X0) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38168 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38168
    | exact resolve eq38168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38168
  have eq38196 : ∀ X0 X1 X2 : G, (σ (k (τ (k X1 X0)) X2)) = (k (k X1 (k (k X0 X0) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38189 X0 X1 X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq38189
    | exact resolve eq38189 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq38189
  have eq38203 : ∀ X0 X1 X2 : G, (k (k X1 X0) (σ X2)) = (k (k X1 (k (k X0 X0) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38196 X0 X1 X2
       have i₂ := eq18 (k X1 X0) X2
       grind)
    | exact superpose eq18 eq38196
    | exact resolve eq38196 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq38196
  have eq44456 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (k X1 (k (k X2 X2) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35987 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35987
    | exact resolve eq35987 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35987
  have eq44843 : ∀ X0 X1 : G, (k X0 (k (k X1 X1) X1)) = (k (k (k X0 (k (k X1 X1) X1)) (k X0 (k (k X1 X1) X1))) (k X0 X1)) ∨ (k X0 (k (k X1 X1) X1)) = (k (k X0 (k (k X1 X1) X1)) (k X0 (k (k X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3163 (k X0 (k (k X1 X1) X1))
       have i₂ := eq44456 (k (k X0 (k (k X1 X1) X1)) (k X0 (k (k X1 X1) X1))) X0 X1
       grind)
    | exact superpose eq44456 eq3163
    | (have j0 := eq3163 (k X0 (k (k X1 X1) X1))
       grind)
    | exact resolve eq3163 eq44456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3163
  have eq44886 : ∀ X0 X1 : G, (k X0 (k (k X1 X1) X1)) = (k (k (k X0 (k (k X1 X1) X1)) (k X0 (k (k X1 X1) X1))) (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq44843 X0 X1
       grind)
    | (have r₁ := eq44843 X0 X1
       have r₂ := eq33785 (k X0 (k (k X1 X1) X1))
       grind)
    | exact resolve eq44843 eq33785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44843
  have eq44967 : ∀ X0 X1 : G, (k X0 (k (k X1 X1) X1)) = (k (k (k X0 (k (k X1 X1) X1)) (k X0 X1)) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44886 X0 X1
       have i₂ := eq44456 (k X0 (k (k X1 X1) X1)) X0 X1
       grind)
    | exact superpose eq44456 eq44886
    | exact resolve eq44886 eq44456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44456 eq44886
  have eq45503 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (k (k X1 (k (k X2 X2) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38203 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38203
    | exact resolve eq38203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38203
  have eq45574 : ∀ X0 X1 : G, (k X0 (k (k X1 X1) X1)) = (k (k (k X0 X1) (k X0 X1)) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44967 X0 X1
       have i₂ := eq45503 (k X0 X1) X0 X1
       grind)
    | exact superpose eq45503 eq44967
    | exact resolve eq44967 eq45503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44967 eq45503
  have eq45621 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ X0) (k (k X1 X1) X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3226 X0 X1
       have i₂ := eq45574 (τ X0) X1
       grind)
    | exact superpose eq45574 eq3226
    | (have j0 := eq3226 X0 X1
       grind)
    | exact resolve eq3226 eq45574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3226 eq45574
  have eq45666 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ X0) (k (k X1 X1) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq45621 X0 X1
       grind)
    | (have r₁ := eq45621 X0 X1
       have r₂ := eq33785 (k X0 (σ X1))
       grind)
    | exact resolve eq45621 eq33785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45621
  have eq45708 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k (k X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45666 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45666
    | exact resolve eq45666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45666
  have eq45892 : ∀ X0 : G, (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = (k (k X0 X0) X0) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8448 X0
       have i₂ := eq45708 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0
       grind)
    | exact superpose eq45708 eq8448
    | (have j0 := eq8448 X0
       grind)
    | exact resolve eq8448 eq45708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8448 eq45708
  have eq45906 : ∀ X0 : G, (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq45892 X0
       grind)
    | (have r₁ := eq45892 X0
       have r₂ := eq33794 X0
       grind)
    | exact resolve eq45892 eq33794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33794 eq45892
  have eq45938 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45906 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq45906
    | exact resolve eq45906 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq45906
  have eq46163 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2840 (k X0 X0) X0
       have i₂ := eq45938 X0
       grind)
    | exact superpose eq45938 eq2840
    | (have j0 := eq2840 X0 X0
       grind)
    | exact resolve eq2840 eq45938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45938
  have eq46523 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (k X0 X0)
       have i₂ := eq46163 X0
       grind)
    | exact superpose eq46163 eq9
    | (have j1 := eq46163 X0
       grind)
    | exact resolve eq9 eq46163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46544 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq173 X0 (k X0 X0) x
       have i₂ := eq46163 X0
       grind)
    | exact superpose eq46163 eq173
    | (have j1 := eq46163 X0
       grind)
    | exact resolve eq173 eq46163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq46851 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46544 X0 X1
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq46544
    | (have j0 := eq46544 X0 X1
       grind)
    | exact resolve eq46544 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq46544
  have eq47417 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46523 X0 X1
       have i₂ := eq46851 X0 X1
       grind)
    | exact superpose eq46851 eq46523
    | (have j0 := eq46523 X0 X1
       have j1 := eq46851 X0 X1
       grind)
    | exact resolve eq46523 eq46851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46523 eq46851
  have eq47603 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47417 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47417
  have eq47819 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33785 X0
       have i₂ := eq47603 X0 X1
       grind)
    | exact superpose eq47603 eq33785
    | (have j1 := eq47603 X0 X1
       grind)
    | exact resolve eq33785 eq47603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47603
  have eq47975 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    grind
  have eq48092 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq46163 X0
       have i₂ := eq47819 X0 (k X0 X0)
       grind)
    | exact superpose eq47819 eq46163
    | (have j0 := eq46163 X0
       have j1 := eq47819 X0 x
       grind)
    | exact resolve eq46163 eq47819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46163 eq47819
  have eq48494 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48092 X0
       have j1 := eq2840 X0 X0
       grind)
    | (have r₁ := eq48092 X0
       have r₂ := eq2840 X0 X0
       grind)
    | (have r₁ := eq48092 (M.op x x)
       have r₂ := eq2840 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq48092 eq2840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840 eq48092
  have eq48563 : ∀ X0 : G, (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq47975 X0
       grind)
    | (have r₁ := eq47975 X0
       have r₂ := eq33785 X0
       grind)
    | exact resolve eq47975 eq33785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47975
  have eq48572 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48494 X0
       grind)
    | (have r₁ := eq48494 X0
       have r₂ := eq33785 X0
       grind)
    | exact resolve eq48494 eq33785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33785 eq48494
  have eq48593 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1352 X0 X1
       have i₂ := eq48572 X0
       grind)
    | exact superpose eq48572 eq1352
    | (have j0 := eq1352 X0 X1
       grind)
    | exact resolve eq1352 eq48572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352 eq48572
  have eq49566 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48593 X0 X1
       grind)
    | (have r₁ := eq48593 X0 X1
       have r₂ := eq48563 (σ X0)
       grind)
    | exact resolve eq48593 eq48563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48563 eq48593
  have eq51535 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49566 x X0
       have i₂ := eq27163
       grind)
    | exact superpose eq27163 eq49566
    | exact resolve eq49566 eq27163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27163 eq49566
  have eq51649 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq142 (σ x) (σ y)
       have i₂ := eq51535 (σ x)
       grind)
    | exact superpose eq51535 eq142
    | exact resolve eq142 eq51535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq51535
  have eq51716 : False := by grind
  exact eq51716

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_y_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
  clear eq36
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq69
    | exact resolve eq69 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq73
    | exact resolve eq73 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq381 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq388 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq14
    | exact resolve eq14 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq710 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq699 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq713 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq710 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq710 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq710 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq710 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq723 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq713
    | (have j0 := eq713 X0 X1
       grind)
    | exact resolve eq713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq1005 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq388
    | exact resolve eq388 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq388
    | exact resolve eq388 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq388
  have eq9132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq75 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9132
    | exact resolve eq9132 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9132
  have eq9144 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq9133
       have r₂ := eq28
       grind)
    | exact resolve eq9133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9133
  have eq9146 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9144
    | exact resolve eq9144 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9144
  have eq9150 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq9146 eq381
    | exact resolve eq381 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9151 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq9146
  have eq9179 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9150
    | exact resolve eq9150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9150
  have eq9183 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9179
  have eq9654 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq9183
       grind)
    | exact superpose eq9183 eq45
    | exact resolve eq45 eq9183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq9183
  have eq9668 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9654
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9654
    | exact resolve eq9654 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9654
  have eq9712 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9668 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq9668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9668
  have eq9715 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9712
    | exact resolve eq9712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9712
  have eq9716 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9715
  have eq9728 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq9716
    | exact resolve eq9716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9716
  have eq9729 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9728
  have eq9940 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9729 eq381
    | exact resolve eq381 eq9729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9729
  have eq9975 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq9940
    | exact resolve eq9940 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9940
  have eq9976 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9975
  have eq9977 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9976 eq28
    | exact resolve eq28 eq9976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9976
  have eq11410 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq9151 eq75
    | exact resolve eq75 eq9151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq9151
  have eq11420 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11410
  have eq11428 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11420
       have r₂ := eq9977
       grind)
    | exact resolve eq11420 eq9977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11420
  have eq12153 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq381 y
       have i₂ := eq11428
       grind)
    | exact superpose eq11428 eq381
    | exact resolve eq381 eq11428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq11428
  have eq12190 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12153
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12153
    | exact resolve eq12153 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12153
  have eq12218 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12190 eq1007
    | exact resolve eq1007 eq12190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12190
  have eq13939 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12218
  have eq14810 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13939 eq56
    | exact resolve eq56 eq13939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq13939
  have eq14854 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq14810
    | exact resolve eq14810 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14810
  have eq14872 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq14854
       grind)
    | exact superpose eq14854 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq14854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14854
  have eq14887 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq14872
  have eq15833 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq14887
       grind)
    | exact superpose eq14887 eq47
    | exact resolve eq47 eq14887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15834 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq14887
       grind)
    | exact superpose eq14887 eq50
    | exact resolve eq50 eq14887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq14887
  have eq15908 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1005 eq15834
    | exact resolve eq15834 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15834
  have eq20939 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15908 eq15833
    | exact resolve eq15833 eq15908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15833 eq15908
  have eq20977 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20939
  have eq20979 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20977
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20977
    | exact resolve eq20977 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20977
  have eq20980 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq20979
  have eq20981 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20980 eq21
    | exact resolve eq21 eq20980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20980
  have eq21120 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20981
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20981
    | exact resolve eq20981 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20981
  have eq21474 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21120 eq9977
    | (have r₁ := eq9977
       have r₂ := eq21120
       grind)
    | exact resolve eq9977 eq21120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9977
  have eq21510 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21474
  have eq21511 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21510
  have eq21578 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21511 eq216
    | exact resolve eq216 eq21511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq21605 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21511 eq1007
    | exact resolve eq1007 eq21511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq21511
  have eq27921 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21605 eq21578
    | exact resolve eq21578 eq21605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21578 eq21605
  have eq27985 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27921
  have eq27989 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq27985
    | exact resolve eq27985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27985
  have eq27994 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27989 eq28
    | exact resolve eq28 eq27989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27989
  have eq28067 : x = (M.op x y) := by
    first
    | (have r₁ := eq27994
       have r₂ := eq21120
       grind)
    | exact resolve eq27994 eq21120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21120 eq27994
  have eq28071 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28067 eq21
    | exact resolve eq21 eq28067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28152 : x = (M.op x x) := by
    first
    | exact superpose eq28067 eq1005
    | exact resolve eq1005 eq28067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq28221 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28071
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28071
    | exact resolve eq28071 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28071
  have eq28233 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq28221 eq27
    | exact resolve eq27 eq28221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq28406 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq28152
       grind)
    | exact superpose eq28152 eq47
    | exact resolve eq47 eq28152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq28430 : x = (k x x) := by grind
  have eq28515 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq28067 eq28406
    | exact resolve eq28406 eq28067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28406
  have eq28537 : y = (M.op x y) := by
    first
    | (have i₁ := eq28515
       have i₂ := eq28152
       grind)
    | exact superpose eq28152 eq28515
    | exact resolve eq28515 eq28152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28152 eq28515
  have eq28549 : y = (M.op x y) := by
    first
    | (have i₁ := eq28537
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28537
    | exact resolve eq28537 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28537
  have eq28554 : x = y := by
    first
    | exact superpose eq28067 eq28549
    | exact resolve eq28549 eq28067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28067 eq28549
  have eq28565 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq28554
       grind)
    | exact superpose eq28554 eq25
    | exact resolve eq25 eq28554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28554
  have eq28723 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28565
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28565
    | exact resolve eq28565 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28565
  have eq28787 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28221 eq28723
    | exact resolve eq28723 eq28221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28723
  have eq29053 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28787 eq28233
    | exact resolve eq28233 eq28787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28233 eq28787
  have eq29469 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq723 x x
       have i₂ := eq28430
       grind)
    | exact superpose eq28430 eq723
    | (have j0 := eq723 x x
       grind)
    | exact resolve eq723 eq28430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq28430
  have eq29474 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29469
  have eq29475 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29474
  have eq29492 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq29475
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29475
    | exact resolve eq29475 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29475
  have eq29511 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28221 eq29492
    | exact resolve eq29492 eq28221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28221 eq29492
  have eq29623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29053 eq29511
    | exact resolve eq29511 eq29053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29053 eq29511
  have eq29624 : False := by grind
  exact eq29624

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq46
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq115
    | exact resolve eq115 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq156 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq210 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq522 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  clear eq53
  have eq530 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq522 X0
       grind)
    | exact superpose eq522 eq14
    | exact resolve eq14 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq94 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq719 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq897 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq530
    | exact resolve eq530 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq899 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq530
    | exact resolve eq530 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq530
  have eq930 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq897 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq897
       grind)
    | exact resolve eq12 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq940 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq930
  have eq943 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq899 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq899
       grind)
    | exact resolve eq12 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq943
  have eq3586 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq719 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq719
    | (have j0 := eq719 (τ X0)
       grind)
    | exact resolve eq719 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq719
  have eq3594 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3586 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3586
    | (have j0 := eq3586 X0
       grind)
    | exact resolve eq3586 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq3600 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3594 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3594
    | (have j0 := eq3594 X0
       grind)
    | exact resolve eq3594 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594
  have eq9435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9435
    | exact resolve eq9435 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9435
  have eq9447 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq9436
       have r₂ := eq28
       grind)
    | exact resolve eq9436 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9436
  have eq9449 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9447
    | exact resolve eq9447 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9447
  have eq9472 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq9449 eq522
    | exact resolve eq522 eq9449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9449
  have eq9475 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9472
    | exact resolve eq9472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9472
  have eq9476 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9475
  have eq9631 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq522 y
       have i₂ := eq9476
       grind)
    | exact superpose eq9476 eq522
    | exact resolve eq522 eq9476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9476
  have eq9634 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9631
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9631
    | exact resolve eq9631 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9631
  have eq9635 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9634
  have eq9666 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9635 eq953
    | exact resolve eq953 eq9635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq9635
  have eq10122 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9666 eq60
    | exact resolve eq60 eq9666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq9666
  have eq10142 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq10122
    | exact resolve eq10122 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10122
  have eq10372 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq10142
  have eq10373 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq10372
    | exact resolve eq10372 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10372
  have eq10407 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10373 eq116
    | exact resolve eq116 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10373
  have eq10418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq10407
  have eq10421 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq10418
       have r₂ := eq75
       grind)
    | exact resolve eq10418 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq10418
  have eq10423 : x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq10421
       have r₂ := eq28
       grind)
    | exact resolve eq10421 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10421
  have eq10629 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq10423
       grind)
    | exact superpose eq10423 eq45
    | exact resolve eq45 eq10423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq10636 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq10423
       grind)
    | exact superpose eq10423 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq10423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10423
  have eq10637 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq10636
  have eq10639 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10637
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10637
    | exact resolve eq10637 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10637
  have eq10646 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10629
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10629
    | exact resolve eq10629 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10629
  have eq10648 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10639
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10639
    | exact resolve eq10639 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10639
  have eq10656 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10646 eq116
    | exact resolve eq116 eq10646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq10665 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq10656
  have eq10933 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq522 y
       have i₂ := eq10648
       grind)
    | exact superpose eq10648 eq522
    | exact resolve eq522 eq10648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10648
  have eq10936 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10933
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10933
    | exact resolve eq10933 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10933
  have eq10937 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq10936
  have eq18353 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq522 y
       have i₂ := eq10665
       grind)
    | exact superpose eq10665 eq522
    | exact resolve eq522 eq10665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10665
  have eq18391 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18353
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18353
    | exact resolve eq18353 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18353
  have eq18392 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18391
  have eq18408 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18392 eq64
    | exact resolve eq64 eq18392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq18392
  have eq18535 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq156 eq18408
    | exact resolve eq18408 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq18408
  have eq18915 : (M.op x y) ≠ (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18535 eq3600
    | (have j0 := eq3600 (M.op x y)
       grind)
    | exact resolve eq3600 eq18535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3600 eq18535
  have eq51905 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq940 eq18915
    | exact resolve eq18915 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq18915
  have eq51911 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq51905
       have r₂ := eq10937
       grind)
    | exact resolve eq51905 eq10937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51905
  have eq55209 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq51911
  have eq55213 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq55209
       have r₂ := eq10937
       grind)
    | exact resolve eq55209 eq10937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10937 eq55209
  have eq55255 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55213 eq210
    | exact resolve eq210 eq55213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq55213
  have eq55338 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq55255
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55255
    | exact resolve eq55255 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55255
  have eq55339 : y = (M.op x y) := by grind
  clear eq55338
  have eq55340 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq55339 eq21
    | exact resolve eq21 eq55339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq55536 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq55340
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq55340
    | exact resolve eq55340 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55340
  have eq55541 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq55536 eq27
    | exact resolve eq27 eq55536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq55545 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq55536 eq52
    | exact resolve eq52 eq55536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55643 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq55536 eq10646
    | exact resolve eq10646 eq55536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10646
  have eq56306 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq55643 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq55643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55643
  have eq56321 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq55541 eq56306
    | exact resolve eq56306 eq55541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56306
  have eq56334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq55541 eq56321
    | exact resolve eq56321 eq55541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56321
  have eq56345 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq56334
       have r₂ := eq28
       grind)
    | exact resolve eq56334 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56334
  have eq61797 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq56345 eq522
    | exact resolve eq522 eq56345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56345
  have eq61861 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq55541 eq61797
    | exact resolve eq61797 eq55541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61797
  have eq61863 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq61861
       have r₂ := eq28
       grind)
    | exact resolve eq61861 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61861
  have eq61871 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq61863
  have eq61937 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61871
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61871
    | exact resolve eq61871 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq61871
  have eq61945 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55339 eq61937
    | exact resolve eq61937 eq55339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55339 eq61937
  have eq62524 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq717 x y
       have i₂ := eq61945
       grind)
    | exact superpose eq61945 eq717
    | (have j0 := eq717 x y
       grind)
    | exact resolve eq717 eq61945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq61945
  have eq62529 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62524
  have eq62535 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62529
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq62529
    | exact resolve eq62529 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62529
  have eq62556 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55536 eq62535
    | exact resolve eq62535 eq55536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62535
  have eq62577 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62556
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62556
    | exact resolve eq62556 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62556
  have eq62596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55541 eq62577
    | exact resolve eq62577 eq55541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62577
  have eq62606 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62596
       have r₂ := eq28
       grind)
    | exact resolve eq62596 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62596
  have eq62616 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62606
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq62606
    | exact resolve eq62606 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq62606
  have eq62625 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55536 eq62616
    | exact resolve eq62616 eq55536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55536 eq62616
  have eq62634 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62625
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62625
    | exact resolve eq62625 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq62625
  have eq62768 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62634 eq522
    | exact resolve eq522 eq62634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq62634
  have eq62832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55541 eq62768
    | exact resolve eq62768 eq55541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62768
  have eq62834 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62832
       have r₂ := eq28
       grind)
    | exact resolve eq62832 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62832
  have eq63210 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq62834 eq899
    | exact resolve eq899 eq62834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq63336 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq63210 eq55545
    | exact resolve eq55545 eq63210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55545
  have eq63431 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq62834 eq63336
    | exact resolve eq63336 eq62834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62834 eq63336
  have eq63463 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq63210 eq63431
    | exact resolve eq63431 eq63210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63210 eq63431
  have eq63485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55541 eq63463
    | exact resolve eq63463 eq55541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55541 eq63463
  have eq63503 : False := by grind
  exact eq63503

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq37
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq209 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq380 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq384 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq380 (M.op X0 X1)
       grind)
    | exact superpose eq380 eq53
    | exact resolve eq53 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq388 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq14
    | exact resolve eq14 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : y = (M.op (M.op y (M.op x y)) y) := by
    first
    | (have i₁ := eq384 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq384
    | (have j0 := eq384 x y
       grind)
    | exact resolve eq384 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq698 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq75 X0 X0
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq713 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq715 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq713 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq713 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq713 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq713 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq724 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq715
    | (have j0 := eq715 X0 X1
       grind)
    | exact resolve eq715 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq970 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq388
    | exact resolve eq388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq388
    | exact resolve eq388 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq975 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq388
    | exact resolve eq388 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq9419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9419
    | exact resolve eq9419 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9419
  have eq9431 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq9420
       have r₂ := eq28
       grind)
    | exact resolve eq9420 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9420
  have eq9433 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9431
    | exact resolve eq9431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9431
  have eq9660 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9433 eq380
    | exact resolve eq380 eq9433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9661 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq9690 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9433 eq970
    | exact resolve eq970 eq9433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9433
  have eq9691 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9690
    | exact resolve eq9690 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9690
  have eq9711 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq380 x
       have i₂ := eq9691
       grind)
    | exact superpose eq9691 eq380
    | exact resolve eq380 eq9691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq9712 : (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9691
  have eq10622 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq9712
       grind)
    | exact superpose eq9712 eq72
    | exact resolve eq72 eq9712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq9712
  have eq10698 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10622
       have i₂ := eq9711
       grind)
    | exact superpose eq9711 eq10622
    | exact resolve eq10622 eq9711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9711 eq10622
  have eq10736 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10698
  have eq10740 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10736
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10736
    | exact resolve eq10736 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10736
  have eq10753 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10740 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10740
  have eq10754 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10753
  have eq10758 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10754
    | exact resolve eq10754 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10754
  have eq10759 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10758
  have eq10824 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10759 eq970
    | exact resolve eq970 eq10759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10759
  have eq10825 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10824
    | exact resolve eq10824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10824
  have eq10826 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10825
  have eq10828 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10826 eq28
    | exact resolve eq28 eq10826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10826
  have eq15656 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9661 eq97
    | exact resolve eq97 eq9661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq9661
  have eq15672 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15656
  have eq15676 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15672 eq9660
    | exact resolve eq9660 eq15672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9660 eq15672
  have eq15714 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq15676
  have eq15770 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq970 x x
       have i₂ := eq15714
       grind)
    | exact superpose eq15714 eq970
    | exact resolve eq970 eq15714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq15714
  have eq15771 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15770
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15770
    | exact resolve eq15770 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15770
  have eq16722 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15771 eq216
    | exact resolve eq216 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16743 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15771 eq975
    | exact resolve eq975 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18666 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16743 eq16722
    | exact resolve eq16722 eq16743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16722 eq16743
  have eq18710 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18666
  have eq18712 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq18710
    | exact resolve eq18710 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18710
  have eq18748 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18712 eq15771
    | exact resolve eq15771 eq18712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771 eq18712
  have eq18751 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18748
  have eq18776 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18751 eq30
    | exact resolve eq30 eq18751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18751
  have eq18942 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq18776
    | exact resolve eq18776 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18776
  have eq18944 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18942 eq29
    | exact resolve eq29 eq18942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18942
  have eq19101 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq18944
    | exact resolve eq18944 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq18944
  have eq19102 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19101
  have eq19108 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19102 eq21
    | exact resolve eq21 eq19102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19102
  have eq19253 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19108
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19108
    | exact resolve eq19108 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19108
  have eq19335 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19253 eq10828
    | (have r₁ := eq10828
       have r₂ := eq19253
       grind)
    | exact resolve eq10828 eq19253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10828
  have eq19363 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19335
  have eq19364 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19363
  have eq19431 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19364 eq216
    | exact resolve eq216 eq19364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq19453 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19364 eq975
    | exact resolve eq975 eq19364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19364
  have eq21625 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19453 eq19431
    | exact resolve eq19431 eq19453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19431 eq19453
  have eq21675 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq21625
  have eq21679 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq21675
    | exact resolve eq21675 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21675
  have eq21682 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21679 eq28
    | exact resolve eq28 eq21679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21679
  have eq21745 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq21682
       have r₂ := eq19253
       grind)
    | exact resolve eq21682 eq19253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19253 eq21682
  have eq21808 : y = (M.op (M.op x x) y) ∨ x = y := by
    first
    | exact superpose eq21745 eq209
    | exact resolve eq209 eq21745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq21841 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21745 eq973
    | exact resolve eq973 eq21745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22866 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq21808
       have i₂ := eq21841
       grind)
    | exact superpose eq21841 eq21808
    | exact resolve eq21808 eq21841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21808 eq21841
  have eq22910 : y = (M.op x y) ∨ x = y := by grind
  clear eq22866
  have eq22912 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq22910
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22910
    | exact resolve eq22910 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22910
  have eq23005 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq22912 eq21745
    | exact resolve eq21745 eq22912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21745 eq22912
  have eq23008 : x = y := by grind
  clear eq23005
  have eq23068 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq23008
       grind)
    | exact superpose eq23008 eq19
    | exact resolve eq19 eq23008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq23069 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq23008
       grind)
    | exact superpose eq23008 eq25
    | exact resolve eq25 eq23008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq23129 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq479
       have i₂ := eq23008
       grind)
    | exact superpose eq23008 eq479
    | exact resolve eq479 eq23008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq23008
  have eq23154 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq973 eq23129
    | exact resolve eq23129 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973 eq23129
  have eq23204 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq23069
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23069
    | exact resolve eq23069 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23069
  have eq23206 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23204 eq27
    | exact resolve eq27 eq23204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23204
  have eq23415 : (M.op (M.op x y) x) = (k (M.op x y) x) := by grind
  clear eq23068
  have eq30662 : x = (k (M.op x y) x) := by
    first
    | exact superpose eq23154 eq23415
    | exact resolve eq23415 eq23154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23154 eq23415
  have eq30685 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq30662 eq708
    | (have j0 := eq708 x (M.op x y)
       grind)
    | exact resolve eq708 eq30662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq30686 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq30662 eq724
    | (have j0 := eq724 x x
       grind)
    | exact resolve eq724 eq30662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq30662
  have eq30689 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq30686
  have eq30690 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq30685
  have eq30695 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq30689
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30689
    | exact resolve eq30689 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30689
  have eq30696 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq30690
    | exact resolve eq30690 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30690
  have eq30712 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23206 eq30695
    | exact resolve eq30695 eq23206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30695
  have eq30713 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq30696
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30696
    | exact resolve eq30696 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30696
  have eq30724 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30712
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30712
    | exact resolve eq30712 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30712
  have eq30725 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq30713
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30713
    | exact resolve eq30713 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq30713
  have eq30736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23206 eq30724
    | exact resolve eq30724 eq23206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30724
  have eq30737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23206 eq30725
    | exact resolve eq30725 eq23206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23206 eq30725
  have eq30746 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq30736
    | exact resolve eq30736 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30736
  have eq30747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq30737
    | exact resolve eq30737 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq30737
  have eq30756 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq30746
       have r₂ := eq28
       grind)
    | exact resolve eq30746 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30746
  have eq30757 : (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq30747
       have r₂ := eq28
       grind)
    | exact resolve eq30747 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30747
  have eq30792 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq30756 eq28
    | exact resolve eq28 eq30756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq30939 : (σ (M.op x y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq30757 eq55
    | exact resolve eq55 eq30757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq31053 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq975 eq30939
    | exact resolve eq30939 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq30939
  have eq31080 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30756 eq31053
    | exact resolve eq31053 eq30756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30756 eq31053
  have eq31098 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30757 eq31080
    | exact resolve eq31080 eq30757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30757 eq31080
  have eq31106 : False := by grind
  exact eq31106

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq184 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq189 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq186 eq16
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) (M.op x y)) X1)) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq558 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq181 eq184
    | exact resolve eq184 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq184
  have eq562 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq558
       grind)
    | exact superpose eq558 eq16
    | exact resolve eq16 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq568 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq186 eq189
    | exact resolve eq189 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq189
  have eq572 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq568 eq16
    | exact resolve eq16 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq580 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq562 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq562
    | exact resolve eq562 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq638 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq664 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq728 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq572 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq572
    | exact resolve eq572 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq868 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq192
    | exact resolve eq192 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq888 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq868 X0
       grind)
    | exact superpose eq868 eq16
    | exact resolve eq16 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq888 (M.op X1 X0) X0
       have i₂ := eq16 X0 X1 X0
       grind)
    | exact superpose eq16 eq888
    | exact resolve eq888 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq888
    | exact resolve eq888 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq888
    | exact resolve eq888 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq888
  have eq957 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq936 eq16
    | exact resolve eq16 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq923 X0 X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq923
    | exact resolve eq923 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq932 X0 X0
       grind)
    | exact superpose eq932 eq180
    | exact resolve eq180 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1335 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq868 (M.op X0 X1)
       grind)
    | exact superpose eq868 eq179
    | exact resolve eq179 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1381 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1010 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq1010
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1010 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1395 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1381 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1407 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1071 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq1071
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1071 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1419 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1407 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq2150 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq638
       grind)
    | exact superpose eq638 eq40
    | exact resolve eq40 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq638
  have eq2151 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2150
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2150
    | exact resolve eq2150 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150
  have eq2153 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2151
    | exact resolve eq2151 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq15418 : ∀ X0 : G, (k (k (k X0 X0) X0) X0) = X0 ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k (k X0 X0) X0) X0
       have i₂ := eq1395 X0
       grind)
    | exact superpose eq1395 eq11
    | (have j0 := eq11 (k (k X0 X0) X0) X0
       have j1 := eq1395 X0
       grind)
    | exact resolve eq11 eq1395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq15452 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1419 eq15418
    | (have j0 := eq15418 X0
       have j1 := eq1419 X0
       grind)
    | exact resolve eq15418 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15418
  have eq15463 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1419 eq15452
    | (have j0 := eq15452 X0
       have j1 := eq1419 X0
       grind)
    | exact resolve eq15452 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15452
  have eq15471 : ∀ X0 : G, (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15463 X0
       have j1 := eq665 X0
       grind)
    | (have r₁ := eq15463 X0
       have r₂ := eq665 X0
       grind)
    | exact resolve eq15463 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq15463
  have eq15474 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1419 eq15471
    | (have j0 := eq15471 X0
       have j1 := eq1419 X0
       grind)
    | exact resolve eq15471 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15471
  have eq15476 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1419 eq15474
    | (have j0 := eq15474 X0
       have j1 := eq1419 X0
       grind)
    | exact resolve eq15474 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419 eq15474
  have eq15478 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15476 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq15476 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (k (M.op x x) (M.op x x))) x
       grind)
    | (have r₁ := eq15476 x
       have r₂ := eq13 (k x x) x
       grind)
    | (have r₁ := eq15476 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq15476 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15476
  have eq16329 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq932 X0 (k X0 X0)
       have i₂ := eq15478 X0
       grind)
    | exact superpose eq15478 eq932
    | (have j1 := eq15478 X0
       grind)
    | exact resolve eq932 eq15478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16378 : y = (M.op y y) ∨ (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq580 (k y y)
       have i₂ := eq15478 y
       grind)
    | exact superpose eq15478 eq580
    | (have j1 := eq15478 y
       grind)
    | exact resolve eq580 eq15478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16389 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq728 (k sF3 sF3)
       have i₂ := eq15478 sF3
       grind)
    | exact superpose eq15478 eq728
    | (have j1 := eq15478 (σ y)
       grind)
    | exact resolve eq728 eq15478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq15478
  have eq16392 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq16389
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq16389
       have r₂ := eq13 (k (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq16389 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16389
  have eq16397 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq16378
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq16378
       have r₂ := eq13 (k y y) y
       grind)
    | exact resolve eq16378 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16378
  have eq16428 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16329 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq16329 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq16329 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq16329 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq16329 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16329
  have eq16543 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq868 X0
       have i₂ := eq16428 X0
       grind)
    | exact superpose eq16428 eq868
    | exact resolve eq868 eq16428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq16548 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq16428 X0
       grind)
    | exact superpose eq16428 eq16
    | exact resolve eq16 eq16428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16549 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq16428 X0
       grind)
    | exact superpose eq16428 eq16
    | exact resolve eq16 eq16428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16758 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16543 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16543
    | exact resolve eq16543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17469 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16758 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16758
    | exact resolve eq16758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19864 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (k X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16549 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16549
    | exact resolve eq16549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2153 eq652
    | exact resolve eq652 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq26958 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26945
       have r₂ := eq27
       grind)
    | exact resolve eq26945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26945
  have eq26967 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16392 eq26958
    | exact resolve eq26958 eq16392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26958
  have eq26972 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq26967
       have i₂ := eq16397
       grind)
    | exact superpose eq16397 eq26967
    | exact resolve eq26967 eq16397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26967
  have eq26980 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26972 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26972
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq26972
       grind)
    | exact resolve eq12 eq26972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26997 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26972 eq932
    | exact resolve eq932 eq26972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26972
  have eq27004 : (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by grind
  clear eq26980
  have eq27010 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16392 eq26997
    | exact resolve eq26997 eq16392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26997
  have eq27024 : (σ x) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16392 eq27004
    | exact resolve eq27004 eq16392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27004
  have eq27025 : (σ x) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by grind
  clear eq27024
  have eq27038 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16392 eq27025
    | exact resolve eq27025 eq16392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16392 eq27025
  have eq27046 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27010 eq27038
    | exact resolve eq27038 eq27010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27038
  have eq27052 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27046 eq2153
    | exact resolve eq2153 eq27046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153 eq27046
  have eq27062 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by grind
  clear eq27052
  have eq27069 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq27062
       have i₂ := eq16397
       grind)
    | exact superpose eq16397 eq27062
    | exact resolve eq27062 eq16397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16397 eq27062
  have eq27070 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (k y y) := by grind
  clear eq27069
  have eq27076 : (τ (σ x)) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (k y y) := by
    first
    | exact superpose eq27070 eq115
    | exact resolve eq115 eq27070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27070
  have eq27159 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq27076
    | exact resolve eq27076 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27076
  have eq27160 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by grind
  clear eq27159
  have eq27181 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq27160
       grind)
    | exact superpose eq27160 eq16
    | exact resolve eq16 eq27160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27223 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq27181 X0
       have i₂ := eq580 X0
       grind)
    | exact superpose eq580 eq27181
    | exact resolve eq27181 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq27181
  have eq29013 : (M.op y x) = (M.op x (M.op y x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1335 y x
       have i₂ := eq27223 x
       grind)
    | exact superpose eq27223 eq1335
    | exact resolve eq1335 eq27223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335 eq27223
  have eq29059 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | exact superpose eq27160 eq29013
    | exact resolve eq29013 eq27160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27160 eq29013
  have eq29073 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29059
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29059
    | exact resolve eq29059 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29059
  have eq29103 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16543 y
       have i₂ := eq29073
       grind)
    | exact superpose eq29073 eq16543
    | exact resolve eq16543 eq29073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16543 eq29073
  have eq29145 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29103
    | exact resolve eq29103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq29103
  have eq29146 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq29145
  have eq29170 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29146 eq28
    | exact resolve eq28 eq29146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq29146
  have eq29266 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq29170
    | exact resolve eq29170 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29170
  have eq29267 : y = (M.op x y) := by grind
  clear eq29266
  have eq29281 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq29267
       grind)
    | exact superpose eq29267 eq24
    | exact resolve eq24 eq29267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq29372 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29281 eq20
    | exact resolve eq20 eq29281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29442 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq29281 eq320
    | exact resolve eq320 eq29281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq166394 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27010 eq29442
    | exact resolve eq29442 eq27010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27010 eq29442
  have eq166472 : y = (k y (M.op x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq166394
    | exact resolve eq166394 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq166394
  have eq166522 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq166472
       have i₂ := eq29267
       grind)
    | exact superpose eq29267 eq166472
    | exact resolve eq166472 eq29267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166472
  have eq166562 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq166522
       have i₂ := eq29267
       grind)
    | exact superpose eq29267 eq166522
    | exact resolve eq166522 eq29267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166522
  have eq166598 : (σ x) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq166562
       have i₂ := eq29267
       grind)
    | exact superpose eq29267 eq166562
    | exact resolve eq166562 eq29267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166562
  have eq171083 : (τ (σ x)) = (k y y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq166598 eq115
    | exact resolve eq115 eq166598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq166598
  have eq171211 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq171083
       have i₂ := eq29267
       grind)
    | exact superpose eq29267 eq171083
    | exact resolve eq171083 eq29267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29267 eq171083
  have eq171239 : x = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq29 eq171211
    | exact resolve eq171211 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq171211
  have eq171240 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq171239
  have eq171325 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq171240 eq16548
    | exact resolve eq16548 eq171240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16548
  have eq171326 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X0) = X0 ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq171240 eq16549
    | exact resolve eq16549 eq171240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16549 eq171240
  have eq171372 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq171325 x
       have i₂ := eq932 sF0 x
       grind)
    | exact superpose eq932 eq171325
    | exact resolve eq171325 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932 eq171325
  have eq174447 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq171372 eq171326
    | exact resolve eq171326 eq171372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171326 eq171372
  have eq174541 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq174447 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174447
  have eq174757 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq923 X0 x
       have i₂ := eq174541 (M.op x X0)
       grind)
    | exact superpose eq174541 eq923
    | (have j1 := eq174541 X0
       grind)
    | exact resolve eq923 eq174541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq174813 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq936 eq174757
    | (have j0 := eq174757 x
       grind)
    | exact resolve eq174757 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174757
  have eq174835 : ∀ X0 : G, x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq174541 eq174813
    | (have j0 := eq174813 X0
       have j1 := eq174541 X0
       grind)
    | exact resolve eq174813 eq174541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174541 eq174813
  have eq174938 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16758 X0
       have i₂ := eq174835 (k X0 X0)
       grind)
    | exact superpose eq174835 eq16758
    | (have j1 := eq174835 X0
       grind)
    | exact resolve eq16758 eq174835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16758 eq174835
  have eq174970 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq174938
    | (have j0 := eq174938 X0
       grind)
    | exact resolve eq174938 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174938
  have eq175013 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq29372 eq174970
    | (have j0 := eq174970 X0
       grind)
    | exact resolve eq174970 eq29372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174970
  have eq175039 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq175013 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq175013
    | (have j0 := eq175013 X0
       grind)
    | exact resolve eq175013 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175013
  have eq175056 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq175039
    | (have j0 := eq175039 X0
       grind)
    | exact resolve eq175039 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175039
  have eq175115 : ∀ X0 : G, (M.op x y) = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq175056 eq957
    | exact resolve eq957 eq175056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq175158 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq175056 eq16428
    | exact resolve eq16428 eq175056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175162 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X1) X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq175056 eq16
    | exact resolve eq16 eq175056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175323 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq175056 eq175162
    | exact resolve eq175162 eq175056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175162
  have eq175480 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq175158 eq19864
    | exact resolve eq19864 eq175158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19864 eq175158
  have eq175500 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq175480
    | (have j0 := eq175480 X0
       grind)
    | exact resolve eq175480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175480
  have eq175540 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29372 eq175500
    | exact resolve eq175500 eq29372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175500
  have eq175575 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq175323 eq175540
    | exact resolve eq175540 eq175323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175323 eq175540
  have eq175985 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (M.op x (σ y)) (M.op x y)) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq175575 eq193
    | exact resolve eq193 eq175575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq175575
  have eq176039 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op x y) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq175115 eq175985
    | exact resolve eq175985 eq175115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175115 eq175985
  have eq176079 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq175056 eq176039
    | exact resolve eq176039 eq175056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175056 eq176039
  have eq176548 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq176079 eq26
    | (have j1 := eq176079 (σ x)
       grind)
    | exact resolve eq26 eq176079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176079
  have eq176582 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq176548
  have eq176587 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq176582 eq27
    | exact resolve eq27 eq176582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176582
  have eq176660 : x = (M.op x y) := by
    first
    | (have r₁ := eq176587
       have r₂ := eq29372
       grind)
    | exact resolve eq176587 eq29372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176587
  have eq176665 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq176660
       grind)
    | exact superpose eq176660 eq22
    | exact resolve eq22 eq176660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq176697 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq936
       have i₂ := eq176660
       grind)
    | exact superpose eq176660 eq936
    | exact resolve eq936 eq176660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq176660
  have eq176935 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq176697
       have i₂ := eq16428 sF0
       grind)
    | exact superpose eq16428 eq176697
    | exact resolve eq176697 eq16428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176697
  have eq177019 : (σ x) = (σ y) := by
    first
    | exact superpose eq176665 eq29281
    | exact resolve eq29281 eq176665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29281
  have eq177020 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq176665 eq20
    | exact resolve eq20 eq176665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176665
  have eq178015 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq177019 eq26
    | exact resolve eq26 eq177019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq178401 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq178015
       have i₂ := eq16428 sF2
       grind)
    | exact superpose eq16428 eq178015
    | exact resolve eq178015 eq16428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178015
  have eq179658 : (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq176935 eq17469
    | exact resolve eq17469 eq176935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17469 eq176935
  have eq179686 : (σ (σ (M.op x y))) = (k (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | (have i₁ := eq179658
       have i₂ := eq16428 (σ (σ sF0))
       grind)
    | exact superpose eq16428 eq179658
    | exact resolve eq179658 eq16428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16428 eq179658
  have eq179732 : (σ (σ (M.op x y))) = (σ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq179686
       have i₂ := eq10 (σ sF0) (σ sF0)
       grind)
    | exact superpose eq10 eq179686
    | exact resolve eq179686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179686
  have eq179768 : (σ (σ (k (M.op x y) (M.op x y)))) = (σ (σ (M.op x y))) := by
    first
    | (have i₁ := eq179732
       have i₂ := eq10 sF0 sF0
       grind)
    | exact superpose eq10 eq179732
    | exact resolve eq179732 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179732
  have eq179796 : (σ (σ (k (M.op x y) (M.op x y)))) = (σ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq179768
    | exact resolve eq179768 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179768
  have eq179821 : (σ (σ (k (M.op x y) (M.op x y)))) = (σ (σ y)) := by
    first
    | exact superpose eq29372 eq179796
    | exact resolve eq179796 eq29372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179796
  have eq179844 : (σ (σ (k (M.op x y) (M.op x y)))) = (σ (σ x)) := by
    first
    | exact superpose eq177019 eq179821
    | exact resolve eq179821 eq177019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179821
  have eq179861 : (σ (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (σ x)) := by
    first
    | exact superpose eq41 eq179844
    | exact resolve eq179844 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq179844
  have eq179874 : (σ (σ x)) = (σ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq29372 eq179861
    | exact resolve eq179861 eq29372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179861
  have eq179885 : (σ (σ x)) = (σ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq177019 eq179874
    | exact resolve eq179874 eq177019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179874
  have eq179891 : (σ (σ x)) = (σ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq20 eq179885
    | exact resolve eq179885 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq179885
  have eq179897 : (σ (σ x)) = (σ (k (σ y) (σ x))) := by
    first
    | exact superpose eq29372 eq179891
    | exact resolve eq179891 eq29372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29372 eq179891
  have eq179903 : (σ (σ x)) = (σ (k (σ x) (σ x))) := by
    first
    | exact superpose eq177019 eq179897
    | exact resolve eq179897 eq177019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177019 eq179897
  have eq179908 : (σ (σ x)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178401 eq179903
    | exact resolve eq179903 eq178401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178401 eq179903
  have eq180181 : (M.op (σ x) (σ y)) = (τ (σ (σ x))) := by
    first
    | exact superpose eq179908 eq15
    | exact resolve eq15 eq179908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179908
  have eq180583 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180181
       have i₂ := eq15 sF2
       grind)
    | exact superpose eq15 eq180181
    | exact resolve eq180181 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180181
  have eq180867 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq180583 eq27
    | exact resolve eq27 eq180583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq180583
  have eq180968 : False := by grind
  exact eq180968

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  clear eq36
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq69
    | exact resolve eq69 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq73
    | exact resolve eq73 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
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
    | exact superpose eq117 eq16
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq158
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq158
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq208 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq206
  have eq380 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq388 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq14
    | exact resolve eq14 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq380 (σ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq380
    | (have j1 := eq65 X0 X0
       grind)
    | exact resolve eq380 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq711 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq696 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq871 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq388
    | exact resolve eq388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq388
    | exact resolve eq388 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq388
  have eq28265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq74 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28265
    | exact resolve eq28265 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28265
  have eq28286 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq28275
       have r₂ := eq28
       grind)
    | exact resolve eq28275 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28275
  have eq28289 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq28286 eq14
    | exact resolve eq14 eq28286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28335 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28286 eq871
    | exact resolve eq871 eq28286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28364 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq28289 x
       have i₂ := eq871 sF3 x
       grind)
    | exact superpose eq871 eq28289
    | exact resolve eq28289 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28289
  have eq28432 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq28335
  have eq35395 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28286 eq28364
    | exact resolve eq28364 eq28286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28364
  have eq35488 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq35395
  have eq35944 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq35488 eq871
    | exact resolve eq871 eq35488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35488
  have eq35948 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq35944
  have eq35967 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq35948 eq28286
    | exact resolve eq28286 eq35948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28286 eq35948
  have eq36025 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq35967
  have eq36031 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq36025
       have r₂ := eq28432
       grind)
    | exact resolve eq36025 eq28432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28432 eq36025
  have eq36549 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq36031
  have eq36630 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq36549 eq74
    | exact resolve eq74 eq36549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq36549
  have eq36650 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by grind
  clear eq36630
  have eq36669 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq36650
       grind)
    | exact superpose eq36650 eq14
    | exact resolve eq14 eq36650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36715 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq871 y x
       have i₂ := eq36650
       grind)
    | exact superpose eq36650 eq871
    | exact resolve eq871 eq36650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36745 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq36669 X0
       have i₂ := eq871 y X0
       grind)
    | exact superpose eq871 eq36669
    | exact resolve eq36669 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36669
  have eq36820 : x ≠ y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by grind
  clear eq36715
  have eq37902 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq36745 x
       have i₂ := eq36650
       grind)
    | exact superpose eq36650 eq36745
    | exact resolve eq36745 eq36650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36745
  have eq37993 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq37902
  have eq38079 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq871 y y
       have i₂ := eq37993
       grind)
    | exact superpose eq37993 eq871
    | exact resolve eq871 eq37993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871 eq37993
  have eq38085 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq38079
  have eq38097 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq36650
       have i₂ := eq38085
       grind)
    | exact superpose eq38085 eq36650
    | exact resolve eq36650 eq38085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36650 eq38085
  have eq38157 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by grind
  clear eq38097
  have eq38163 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq38157
       have r₂ := eq36820
       grind)
    | exact resolve eq38157 eq36820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36820 eq38157
  have eq38176 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq38163
       grind)
    | exact superpose eq38163 eq108
    | exact resolve eq108 eq38163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq38178 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq380 y
       have i₂ := eq38163
       grind)
    | exact superpose eq38163 eq380
    | exact resolve eq380 eq38163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq38163
  have eq38242 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq38178
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq38178
    | exact resolve eq38178 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38178
  have eq38243 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq38176
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38176
    | exact resolve eq38176 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38176
  have eq38245 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38242 eq29
    | exact resolve eq29 eq38242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38242
  have eq38420 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq38245
    | exact resolve eq38245 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38245
  have eq38421 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38420 eq21
    | exact resolve eq21 eq38420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38437 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38420 eq117
    | exact resolve eq117 eq38420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq38530 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq38420
  have eq38579 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38437
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq38437
    | exact resolve eq38437 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq38437
  have eq38593 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38421
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38421
    | exact resolve eq38421 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38421
  have eq44241 : (τ (σ x)) = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38243 eq107
    | exact resolve eq107 eq38243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq44260 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38243 eq38579
    | exact resolve eq38579 eq38243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38243 eq38579
  have eq44299 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq44260
       have r₂ := eq38530
       grind)
    | exact resolve eq44260 eq38530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44260
  have eq44307 : x = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq44241
    | exact resolve eq44241 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44241
  have eq45776 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq711 y
       have i₂ := eq44307
       grind)
    | exact superpose eq44307 eq711
    | (have j0 := eq711 y
       grind)
    | exact resolve eq711 eq44307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq44307
  have eq46012 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq45776
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq45776
    | exact resolve eq45776 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45776
  have eq46036 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq46012
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq46012
    | exact resolve eq46012 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46012
  have eq46052 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq46036
    | exact resolve eq46036 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46036
  have eq46055 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq46052
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq46052
    | exact resolve eq46052 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46052
  have eq151708 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38593 eq46055
    | exact resolve eq46055 eq38593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38593 eq46055
  have eq151814 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq151708
       have r₂ := eq38530
       grind)
    | exact resolve eq151708 eq38530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38530 eq151708
  have eq151822 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq151814
       have r₂ := eq28
       grind)
    | exact resolve eq151814 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151814
  have eq151835 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq151822
  have eq152761 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq151835 eq44299
    | exact resolve eq44299 eq151835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44299 eq151835
  have eq152797 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq152761
  have eq152824 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq152797 eq29
    | exact resolve eq29 eq152797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq152797
  have eq153084 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq152824
    | exact resolve eq152824 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq152824
  have eq153085 : x = (M.op x y) := by grind
  clear eq153084
  have eq153087 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq153085 eq21
    | exact resolve eq21 eq153085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq153185 : x = (M.op x x) := by
    first
    | exact superpose eq153085 eq873
    | exact resolve eq873 eq153085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq153441 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq153087
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq153087
    | exact resolve eq153087 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153087
  have eq153461 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq153441 eq27
    | exact resolve eq27 eq153441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq153706 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq153185
       grind)
    | exact superpose eq153185 eq47
    | exact resolve eq47 eq153185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq153734 : x = (k x x) := by grind
  have eq153847 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq153085 eq153706
    | exact resolve eq153706 eq153085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153706
  have eq153876 : y = (M.op x y) := by
    first
    | (have i₁ := eq153847
       have i₂ := eq153185
       grind)
    | exact superpose eq153185 eq153847
    | exact resolve eq153847 eq153185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153185 eq153847
  have eq153894 : y = (M.op x y) := by
    first
    | (have i₁ := eq153876
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq153876
    | exact resolve eq153876 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq153876
  have eq153901 : x = y := by
    first
    | exact superpose eq153085 eq153894
    | exact resolve eq153894 eq153085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153894
  have eq153915 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq153901
       grind)
    | exact superpose eq153901 eq25
    | exact resolve eq25 eq153901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq153901
  have eq154354 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq153915
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq153915
    | exact resolve eq153915 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153915
  have eq154496 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq153441 eq154354
    | exact resolve eq154354 eq153441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154354
  have eq154984 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq154496 eq153461
    | exact resolve eq153461 eq154496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153461 eq154496
  have eq155212 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq154984 eq208
    | exact resolve eq208 eq154984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq154984
  have eq155293 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq155212
       have r₂ := eq28
       grind)
    | exact resolve eq155212 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155212
  have eq155295 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq153085 eq155293
    | exact resolve eq155293 eq153085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153085 eq155293
  have eq155297 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq155295
       have i₂ := eq153734
       grind)
    | exact superpose eq153734 eq155295
    | exact resolve eq155295 eq153734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153734 eq155295
  have eq155300 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq155297 eq15
    | exact resolve eq15 eq155297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155297
  have eq155694 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq155300
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq155300
    | exact resolve eq155300 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq155300
  have eq155833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153441 eq155694
    | exact resolve eq155694 eq153441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153441 eq155694
  have eq155917 : False := by grind
  exact eq155917

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  clear eq36
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
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
    | exact superpose eq117 eq16
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq158
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq158
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq208 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq206
  have eq515 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq523 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq515 X0
       grind)
    | exact superpose eq515 eq14
    | exact resolve eq14 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq515 (σ X0)
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq515
    | (have j1 := eq71 X0 X0
       grind)
    | exact resolve eq515 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq711 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq696 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq871 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq523
    | exact resolve eq523 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq523
    | exact resolve eq523 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq523
  have eq28247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq28257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28247
    | exact resolve eq28247 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28247
  have eq28268 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq28257
       have r₂ := eq28
       grind)
    | exact resolve eq28257 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28257
  have eq28270 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28268 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq28268
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq28268
       grind)
    | exact resolve eq12 eq28268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28268
  have eq28320 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq28270
  have eq28321 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq28320
  have eq28776 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28321 eq60
    | exact resolve eq60 eq28321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28321
  have eq28809 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq28776
    | exact resolve eq28776 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28776
  have eq28813 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq28809
       have r₂ := eq12 x y
       grind)
    | exact resolve eq28809 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28809
  have eq28820 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq28813
  have eq29340 : (τ (σ x)) = (k x y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28820 eq60
    | exact resolve eq60 eq28820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq28820
  have eq29372 : x = (k x y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq29340
    | exact resolve eq29340 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29340
  have eq29373 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq29372
  have eq29639 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq29373
       grind)
    | exact superpose eq29373 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq29373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29373
  have eq29650 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq29639
  have eq29661 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29650
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29650
    | exact resolve eq29650 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29650
  have eq29770 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq29661
       grind)
    | exact superpose eq29661 eq14
    | exact resolve eq14 eq29661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29816 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq871 y x
       have i₂ := eq29661
       grind)
    | exact superpose eq29661 eq871
    | exact resolve eq871 eq29661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29845 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq29770 X0
       have i₂ := eq871 y X0
       grind)
    | exact superpose eq871 eq29770
    | exact resolve eq29770 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29770
  have eq30004 : x ≠ y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq29816
  have eq32596 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29845 x
       have i₂ := eq29661
       grind)
    | exact superpose eq29661 eq29845
    | exact resolve eq29845 eq29661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29845
  have eq32684 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq32596
  have eq32763 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq871 y y
       have i₂ := eq32684
       grind)
    | exact superpose eq32684 eq871
    | exact resolve eq871 eq32684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871 eq32684
  have eq32766 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq32763
  have eq32775 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29661
       have i₂ := eq32766
       grind)
    | exact superpose eq32766 eq29661
    | exact resolve eq29661 eq32766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29661 eq32766
  have eq32828 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq32775
  have eq32831 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq32828
       have r₂ := eq30004
       grind)
    | exact resolve eq32828 eq30004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30004 eq32828
  have eq33176 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq32831
       grind)
    | exact superpose eq32831 eq108
    | exact resolve eq108 eq32831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq33178 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq515 y
       have i₂ := eq32831
       grind)
    | exact superpose eq32831 eq515
    | exact resolve eq515 eq32831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515 eq32831
  have eq33237 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33178
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33178
    | exact resolve eq33178 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33178
  have eq33238 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33176
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33176
    | exact resolve eq33176 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33176
  have eq33239 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33237 eq21
    | exact resolve eq21 eq33237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33255 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33237 eq117
    | exact resolve eq117 eq33237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq33346 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq33237
  have eq33396 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33255
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq33255
    | exact resolve eq33255 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq33255
  have eq33410 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33239
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33239
    | exact resolve eq33239 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33239
  have eq36289 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq33238
       have r₂ := eq33346
       grind)
    | exact resolve eq33238 eq33346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33238 eq33346
  have eq36301 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36289 eq107
    | exact resolve eq107 eq36289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq36312 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36289 eq33396
    | exact resolve eq33396 eq36289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33396 eq36289
  have eq36343 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq36312
  have eq36358 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq36301
    | exact resolve eq36301 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36301
  have eq45492 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq711 y
       have i₂ := eq36358
       grind)
    | exact superpose eq36358 eq711
    | (have j0 := eq711 y
       grind)
    | exact resolve eq711 eq36358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq36358
  have eq45710 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45492
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq45492
    | exact resolve eq45492 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45492
  have eq45734 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45710
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45710
    | exact resolve eq45710 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45710
  have eq45749 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq45734
    | exact resolve eq45734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45734
  have eq45753 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45749
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq45749
    | exact resolve eq45749 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45749
  have eq45755 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33410 eq45753
    | exact resolve eq45753 eq33410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33410 eq45753
  have eq45822 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq45755
  have eq45849 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq45822
       have r₂ := eq28
       grind)
    | exact resolve eq45822 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45822
  have eq45864 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq45849
  have eq45984 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45864 eq36343
    | exact resolve eq36343 eq45864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36343 eq45864
  have eq46013 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq45984
  have eq46358 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46013 eq29
    | exact resolve eq29 eq46013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq46013
  have eq46567 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq46358
    | exact resolve eq46358 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq46358
  have eq46568 : x = (M.op x y) := by grind
  clear eq46567
  have eq46570 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq46568 eq21
    | exact resolve eq21 eq46568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq46668 : x = (M.op x x) := by
    first
    | exact superpose eq46568 eq873
    | exact resolve eq873 eq46568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq46760 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq46570
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq46570
    | exact resolve eq46570 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46570
  have eq46772 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq46760 eq27
    | exact resolve eq27 eq46760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq46966 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq46668
       grind)
    | exact superpose eq46668 eq47
    | exact resolve eq47 eq46668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq46992 : x = (k x x) := by grind
  have eq47105 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq46568 eq46966
    | exact resolve eq46966 eq46568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46966
  have eq47133 : y = (M.op x y) := by
    first
    | (have i₁ := eq47105
       have i₂ := eq46668
       grind)
    | exact superpose eq46668 eq47105
    | exact resolve eq47105 eq46668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46668 eq47105
  have eq47150 : y = (M.op x y) := by
    first
    | (have i₁ := eq47133
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47133
    | exact resolve eq47133 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq47133
  have eq47157 : x = y := by
    first
    | exact superpose eq46568 eq47150
    | exact resolve eq47150 eq46568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47150
  have eq47171 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq47157
       grind)
    | exact superpose eq47157 eq25
    | exact resolve eq25 eq47157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq47157
  have eq47413 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq47171
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq47171
    | exact resolve eq47171 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47171
  have eq47489 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq46760 eq47413
    | exact resolve eq47413 eq46760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47413
  have eq47840 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq47489 eq46772
    | exact resolve eq46772 eq47489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46772 eq47489
  have eq48030 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47840 eq208
    | exact resolve eq208 eq47840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq47840
  have eq48107 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq48030
       have r₂ := eq28
       grind)
    | exact resolve eq48030 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48030
  have eq48108 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq46568 eq48107
    | exact resolve eq48107 eq46568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46568 eq48107
  have eq48109 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq48108
       have i₂ := eq46992
       grind)
    | exact superpose eq46992 eq48108
    | exact resolve eq48108 eq46992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46992 eq48108
  have eq48111 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48109 eq15
    | exact resolve eq15 eq48109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48109
  have eq48211 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq48111
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48111
    | exact resolve eq48111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq48111
  have eq48246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46760 eq48211
    | exact resolve eq48211 eq46760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46760 eq48211
  have eq48270 : False := by grind
  exact eq48270
