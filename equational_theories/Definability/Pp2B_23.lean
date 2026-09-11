import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pxx_pxy_Equation2653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
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
  have eq52 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq78
    | exact resolve eq78 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq86
    | exact resolve eq86 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq108 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq371 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 X0)
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq374 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq3057 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq379 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq379
    | exact resolve eq379 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq3063 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq3057
    | exact resolve eq3057 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057
  have eq3067 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3063 X0
       have i₂ := eq52 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq3063
    | exact resolve eq3063 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063
  have eq3070 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3067 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq3067
    | exact resolve eq3067 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3067
  have eq3072 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3070 (M.op X0 X0)
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq3070
    | exact resolve eq3070 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3079 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3072 X0
       have i₂ := eq3070 X0
       grind)
    | exact superpose eq3070 eq3072
    | exact resolve eq3072 eq3070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3072
  have eq3216 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq505 X0
       have j1 := eq372 X0
       grind)
    | (have r₁ := eq505 X0
       have r₂ := eq372 X0
       grind)
    | exact resolve eq505 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq505
  have eq3577 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq3070 X0
       grind)
    | exact superpose eq3070 eq371
    | exact resolve eq371 eq3070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq3070
  have eq3673 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq3577 X0
       grind)
    | exact superpose eq3577 eq14
    | exact resolve eq14 eq3577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3674 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq3577 X0
       grind)
    | exact superpose eq3577 eq14
    | exact resolve eq14 eq3577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10669 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0
       have i₂ := eq3673 X0 X1
       grind)
    | exact superpose eq3673 eq374
    | exact resolve eq374 eq3673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq3673
  have eq10710 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10669 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq3577 X0
       grind)
    | exact superpose eq3577 eq10669
    | exact resolve eq10669 eq3577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3577
  have eq10729 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10669 (M.op X0 X0) x
       have i₂ := eq14 X0 x
       grind)
    | exact superpose eq14 eq10669
    | exact resolve eq10669 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10669
  have eq11682 : x = (M.op (M.op (M.op x y) (M.op (M.op y y) y)) x) := by
    first
    | (have i₁ := eq10710 y x
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq10710
    | (have j0 := eq10710 y x
       grind)
    | exact resolve eq10710 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11684 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y))) (σ x)) := by
    first
    | exact superpose eq28 eq10710
    | (have j0 := eq10710 (σ y) (σ x)
       grind)
    | exact resolve eq10710 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10710
  have eq16459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16459
    | exact resolve eq16459 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16459
  have eq16471 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16460
       have r₂ := eq29
       grind)
    | exact resolve eq16460 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16460
  have eq16521 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16471 eq10729
    | exact resolve eq10729 eq16471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16471
  have eq16528 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16521
    | exact resolve eq16521 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16521
  have eq16543 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq16528
  have eq16620 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16543
    | exact resolve eq16543 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16543
  have eq17353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16620 eq87
    | exact resolve eq87 eq16620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16620
  have eq17361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17353
  have eq17363 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17361
       have r₂ := eq29
       grind)
    | exact resolve eq17361 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17361
  have eq17413 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10729 x
       have i₂ := eq17363
       grind)
    | exact superpose eq17363 eq10729
    | exact resolve eq10729 eq17363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17363
  have eq17420 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17413
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq17413
    | exact resolve eq17413 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17413
  have eq17692 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17420
  have eq17769 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17692
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq17692
    | exact resolve eq17692 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17692
  have eq18286 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq17769
       grind)
    | exact superpose eq17769 eq46
    | exact resolve eq46 eq17769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17769
  have eq18304 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq18286
    | exact resolve eq18286 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18286
  have eq19007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18304 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq18304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq19007
    | exact resolve eq19007 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19007
  have eq19021 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19010
       have r₂ := eq29
       grind)
    | exact resolve eq19010 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19010
  have eq89949 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19021 eq10729
    | exact resolve eq10729 eq19021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19021
  have eq89964 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq89949
    | exact resolve eq89949 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89949
  have eq89965 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq89964
  have eq90559 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq89965
  have eq90659 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq90559
    | exact resolve eq90559 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90559
  have eq91068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq90659 eq18304
    | exact resolve eq18304 eq90659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18304 eq90659
  have eq91080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq91068
  have eq91090 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq91080
       have r₂ := eq29
       grind)
    | exact resolve eq91080 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91080
  have eq91092 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq91090 eq29
    | exact resolve eq29 eq91090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91093 : (σ x) = (M.op (M.op (σ y) (M.op (M.op (σ y) (σ y)) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq91090 eq11684
    | exact resolve eq11684 eq91090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11684 eq91090
  have eq91096 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq91093
       have i₂ := eq3079 sF3
       grind)
    | exact superpose eq3079 eq91093
    | exact resolve eq91093 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91093
  have eq91107 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq91096 eq3674
    | exact resolve eq3674 eq91096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91096
  have eq91114 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq91107
       have i₂ := eq3079 sF2
       grind)
    | exact superpose eq3079 eq91107
    | exact resolve eq91107 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91107
  have eq91153 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq91114 eq3216
    | exact resolve eq3216 eq91114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91114
  have eq91218 : (τ (σ y)) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq91153 eq56
    | exact resolve eq56 eq91153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq91219 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq91153 eq87
    | exact resolve eq87 eq91153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq91153
  have eq91264 : y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq91219
       have r₂ := eq91092
       grind)
    | exact resolve eq91219 eq91092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91092 eq91219
  have eq91265 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq91218
    | exact resolve eq91218 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq91218
  have eq101059 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10729 x
       have i₂ := eq91264
       grind)
    | exact superpose eq91264 eq10729
    | exact resolve eq10729 eq91264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91264
  have eq101117 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101059
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq101059
    | exact resolve eq101059 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101059
  have eq101118 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq101117
  have eq101176 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq101118
  have eq101324 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101176
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq101176
    | exact resolve eq101176 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq101176
  have eq102497 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq91265
       have i₂ := eq101324
       grind)
    | exact superpose eq101324 eq91265
    | exact resolve eq91265 eq101324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91265 eq101324
  have eq102501 : y = (M.op x y) := by grind
  clear eq102497
  have eq102544 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq102501 eq22
    | exact resolve eq22 eq102501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq102683 : x = (M.op (M.op y (M.op (M.op y y) y)) x) := by
    first
    | exact superpose eq102501 eq11682
    | exact resolve eq11682 eq102501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11682 eq102501
  have eq102690 : x = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq102683
       have i₂ := eq3079 y
       grind)
    | exact superpose eq3079 eq102683
    | exact resolve eq102683 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102683
  have eq102822 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq102544
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq102544
    | exact resolve eq102544 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102544
  have eq102824 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq102822 eq28
    | exact resolve eq28 eq102822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq103124 : y = (M.op x (M.op (M.op x x) x)) := by
    first
    | (have i₁ := eq3674 x y
       have i₂ := eq102690
       grind)
    | exact superpose eq102690 eq3674
    | exact resolve eq3674 eq102690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674 eq102690
  have eq103132 : y = (M.op x x) := by
    first
    | (have i₁ := eq103124
       have i₂ := eq3079 x
       grind)
    | exact superpose eq3079 eq103124
    | exact resolve eq103124 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3079 eq103124
  have eq103212 : y = (k x y) := by
    first
    | (have i₁ := eq3216 x
       have i₂ := eq103132
       grind)
    | exact superpose eq103132 eq3216
    | exact resolve eq3216 eq103132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3216 eq103132
  have eq103285 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq103212
       grind)
    | exact superpose eq103212 eq46
    | exact resolve eq46 eq103212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq103212
  have eq103343 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq102822 eq103285
    | exact resolve eq103285 eq102822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103285
  have eq103356 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq103343
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq103343
    | exact resolve eq103343 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq103343
  have eq103367 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq102822 eq103356
    | exact resolve eq103356 eq102822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102822 eq103356
  have eq103382 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq103367 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq103367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq102824 eq103382
    | exact resolve eq103382 eq102824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103382
  have eq103395 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq103383
       have r₂ := eq29
       grind)
    | exact resolve eq103383 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103383
  have eq120805 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq103395
  have eq120915 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq102824 eq120805
    | exact resolve eq120805 eq102824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120805
  have eq120929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq103367 eq120915
    | exact resolve eq120915 eq103367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103367 eq120915
  have eq120933 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq120929
       have r₂ := eq29
       grind)
    | exact resolve eq120929 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120929
  have eq121018 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq120933 eq10729
    | exact resolve eq10729 eq120933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10729 eq120933
  have eq121029 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102824 eq121018
    | exact resolve eq121018 eq102824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102824 eq121018
  have eq121040 : False := by grind
  exact eq121040

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxx_pyx_pxy_Equation2653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    grind
  have eq35 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (k (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    grind
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (k (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    grind
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq49 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq49
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq87 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq100 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq30 X0 (σ X0)
       have i₂ := eq92 (σ X0)
       grind)
    | exact superpose eq92 eq30
    | exact resolve eq30 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq101 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq92 (τ X0)
       grind)
    | exact superpose eq92 eq37
    | exact resolve eq37 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq102 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq92 (τ X0)
       grind)
    | exact superpose eq92 eq18
    | exact resolve eq18 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq102
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq101 X0
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq101
    | exact resolve eq101 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq100 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq103
    | exact resolve eq103 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq105
    | exact resolve eq105 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq105
  have eq115 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (M.op X0 X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq123 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq125 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq111
    | exact resolve eq111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq146 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (k (M.op (M.op X0 X0) X0) (M.op X0 X0))) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X0 X0) X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq35
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq167 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (M.op X0 X0) X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq36
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq176 : ∀ X0 : G, (M.op (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op (M.op X0 X0) X0) (M.op X0 X0))) = (k (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq33 (M.op X0 X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq33
    | exact resolve eq33 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (k (M.op X0 X0) X0) (M.op X0 X0))) = (M.op (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (k (M.op X0 X0) X0)
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq24
    | exact resolve eq24 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq33
  have eq205 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq9
    | exact resolve eq9 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (M.op (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq64
    | exact resolve eq64 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq243 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq64
    | exact resolve eq64 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq267 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (σ (M.op X0 X0))) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq9
    | exact resolve eq9 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (σ X0) = (M.op (k (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq34
    | exact resolve eq34 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq286 : ∀ X0 : G, (σ X0) = (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq271
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq609 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq286 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq286
    | exact resolve eq286 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq613 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq117 (τ X0)
       grind)
    | exact superpose eq117 eq19
    | exact resolve eq19 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq613 X0
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq613
    | exact resolve eq613 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq623 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq615 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq615
    | exact resolve eq615 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq629 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq623 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq623
    | exact resolve eq623 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq1020 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 X1) X1) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq125 X1 (σ X0)
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq125
    | exact resolve eq125 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq1052 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq629 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq629
    | exact resolve eq629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1059 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ (M.op X0 X0)) (τ X0))
       have i₂ := eq629 X0
       grind)
    | exact superpose eq629 eq10
    | exact resolve eq10 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq1084 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1052 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq1052
    | exact resolve eq1052 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq1052
  have eq1090 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1084 X0
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq1084
    | exact resolve eq1084 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1280 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq238 X0 X1 X2
       have i₂ := eq133 X2
       grind)
    | exact superpose eq133 eq238
    | (have j0 := eq238 X0 X1 X2
       grind)
    | exact resolve eq238 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq1308 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq1280 X0 X1 X2
       grind)
    | exact superpose eq1280 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq1280 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq1280 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq1280 X0 X1 X2
       grind)
    | exact resolve eq13 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1311 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1308 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1315 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op X2 X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1311 X0 X1 X2
       have i₂ := eq133 X2
       grind)
    | exact superpose eq133 eq1311
    | (have j0 := eq1311 X0 X1 X2
       grind)
    | exact resolve eq1311 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1316 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op X2 X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1315 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1336 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1316 X0 X1 X2
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq1316
    | (have j0 := eq1316 X0 X1 X2
       grind)
    | exact resolve eq1316 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1316
  have eq1337 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1336 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1698 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (M.op (k (σ X1) X2) (k (σ X1) X2)) ∨ (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k (σ X0) X1)
       have i₂ := eq243 X0 X1 X2
       grind)
    | exact superpose eq243 eq13
    | (have j0 := eq13 (σ X0) (k (σ X1) X2)
       have j1 := eq243 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq243 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq243 X0 X1 X2
       grind)
    | exact resolve eq13 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq1707 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (M.op (k (σ X1) X2) (k (σ X1) X2)) ∨ (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1698 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1708 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (k (σ X1) X2) (k (σ X1) X2)) ∨ (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1707 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq1713 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (M.op (k (σ X1) X2) (k (σ X1) X2)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1708 X0 X1 X2
       have i₂ := eq28 X1 X2 X0
       grind)
    | exact superpose eq28 eq1708
    | (have j0 := eq1708 X0 X1 X2
       grind)
    | exact resolve eq1708 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1708
  have eq1714 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1713 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1918 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq123 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq123
    | exact resolve eq123 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq123
  have eq1937 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq1918 X0
       grind)
    | exact superpose eq1918 eq146
    | exact resolve eq146 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq1940 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq1918 X0
       grind)
    | exact superpose eq1918 eq167
    | exact resolve eq167 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq2871 : ∀ X0 : G, (k (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq1918 X0
       grind)
    | exact superpose eq1918 eq176
    | exact resolve eq176 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2879 : ∀ X0 : G, (M.op (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op (M.op X0 X0) X0) (M.op X0 X0))) = (M.op (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq184 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq184
    | exact resolve eq184 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq2880 : ∀ X0 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2879 X0
       have i₂ := eq1918 X0
       grind)
    | exact superpose eq1918 eq2879
    | exact resolve eq2879 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2879
  have eq3070 : ∀ X0 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1020 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq267 (M.op X0 X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact superpose eq267 eq1020
    | exact resolve eq1020 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq1020
  have eq3084 : ∀ X0 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) = (σ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3070 X0
       have i₂ := eq133 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq133 eq3070
    | exact resolve eq3070 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq3070
  have eq3097 : ∀ X0 : G, (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    grind
  clear eq3084
  have eq3104 : ∀ X0 : G, (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) = (σ (k (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    grind
  clear eq3097
  have eq3108 : ∀ X0 : G, (σ (k (M.op (M.op X0 X0) X0) (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3104 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq3104
    | exact resolve eq3104 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq3104
  have eq3110 : ∀ X0 : G, (σ X0) = (σ (k (M.op (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3108 X0
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq3108
    | exact resolve eq3108 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq3108
  have eq3112 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3110 X0
       have i₂ := eq1918 X0
       grind)
    | exact superpose eq1918 eq3110
    | exact resolve eq3110 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110
  have eq3237 : ∀ X0 : G, (σ (τ X0)) = (σ (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3112 (τ X0)
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq3112
    | exact resolve eq3112 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3239 : ∀ X0 : G, (τ (σ X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))
       have i₂ := eq3112 X0
       grind)
    | exact superpose eq3112 eq10
    | exact resolve eq10 eq3112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3311 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3239 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3239
    | exact resolve eq3239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239
  have eq3313 : ∀ X0 : G, (σ (τ X0)) = (σ (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3237 X0
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq3237
    | exact resolve eq3237 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059 eq3237
  have eq3321 : ∀ X0 : G, (σ (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3313 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3313
    | exact resolve eq3313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3313
  have eq3333 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1937 X0 X1
       have i₂ := eq3311 X0
       grind)
    | exact superpose eq3311 eq1937
    | exact resolve eq1937 eq3311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq3334 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1940 X0 X1
       have i₂ := eq3311 X0
       grind)
    | exact superpose eq3311 eq1940
    | exact resolve eq1940 eq3311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq3340 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2871 X0
       have i₂ := eq3311 X0
       grind)
    | exact superpose eq3311 eq2871
    | exact resolve eq2871 eq3311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871
  have eq3341 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2880 X0
       have i₂ := eq3311 X0
       grind)
    | exact superpose eq3311 eq2880
    | exact resolve eq2880 eq3311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2880
  have eq3787 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (M.op (τ X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq205 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq3333 X0 X0
       grind)
    | exact superpose eq3333 eq205
    | exact resolve eq205 eq3333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq3860 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op X0 X0) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3340 (M.op (M.op X0 X0) X0)
       have i₂ := eq3333 X0 X0
       grind)
    | exact superpose eq3333 eq3340
    | exact resolve eq3340 eq3333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3333 eq3340
  have eq3866 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3860 X0
       have i₂ := eq3341 X0
       grind)
    | exact superpose eq3341 eq3860
    | exact resolve eq3860 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341 eq3860
  have eq4414 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op X1 X1)) X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3866 X0
       have i₂ := eq3334 X0 X1
       grind)
    | exact superpose eq3334 eq3866
    | exact resolve eq3866 eq3334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334
  have eq5367 : ∀ X0 X1 : G, (τ X0) = (k (M.op (M.op (τ X0) (M.op X1 X1)) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4414 (τ X0) X1
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq4414
    | exact resolve eq4414 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq4414
  have eq8495 : ∀ X0 X1 X2 : G, (σ (k (k X0 X1) X2)) = (M.op (k (σ X0) (σ X1)) (σ X2)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1337 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1337
    | (have j0 := eq1337 (σ X0) X1 X2
       grind)
    | exact resolve eq1337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq8602 : ∀ X0 X1 X2 : G, (σ (k (k X0 X1) X2)) = (M.op (σ (k X0 X1)) (σ X2)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8495 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8495
    | (have j0 := eq8495 X0 X1 X2
       grind)
    | exact resolve eq8495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8495
  have eq8624 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X2 X2)) ∨ (σ (k (k X0 X1) X2)) = (M.op (σ (k X0 X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8602 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8602
    | (have j0 := eq8602 X0 X1 X2
       grind)
    | exact resolve eq8602 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8602
  have eq9946 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (M.op X0 X0) X0)
       have i₂ := eq3787 X0 X1
       grind)
    | exact superpose eq3787 eq11
    | exact resolve eq11 eq3787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3787
  have eq27493 : ∀ X0 X1 : G, (k (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3866 X0
       have i₂ := eq9946 X0 X1
       grind)
    | exact superpose eq9946 eq3866
    | exact resolve eq3866 eq9946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3866 eq9946
  have eq50653 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) (k (σ (M.op (M.op (τ X0) (M.op X2 X2)) X2)) (M.op X0 X0))) ∨ (σ X1) = (M.op (k (σ (M.op (M.op (τ X0) (M.op X2 X2)) X2)) (M.op X0 X0)) (k (σ (M.op (M.op (τ X0) (M.op X2 X2)) X2)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1714 X1 (M.op (M.op (τ X0) (M.op X2 X2)) X2) (M.op X0 X0)
       have i₂ := eq5367 X0 X2
       grind)
    | exact superpose eq5367 eq1714
    | (have j0 := eq1714 X1 (M.op (M.op (τ X0) (M.op X2 X2)) X2) (M.op X0 X0)
       grind)
    | exact resolve eq1714 eq5367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714 eq5367
  have eq50667 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (k (σ (M.op (M.op (τ X0) (M.op X2 X2)) X2)) (M.op X0 X0)) (k (σ (M.op (M.op (τ X0) (M.op X2 X2)) X2)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50653 X0 X1 X2
       have i₂ := eq27493 X0 X2
       grind)
    | exact superpose eq27493 eq50653
    | (have j0 := eq50653 X0 X1 X2
       grind)
    | exact resolve eq50653 eq27493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50653
  have eq50721 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (k (σ (M.op (M.op (τ X0) (M.op X2 X2)) X2)) (M.op X0 X0)) (k (σ (M.op (M.op (τ X0) (M.op X2 X2)) X2)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50667 X0 X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq50667
    | (have j0 := eq50667 X0 X1 X2
       grind)
    | exact resolve eq50667 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq50667
  have eq50766 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50721 X0 X1 X1
       have i₂ := eq27493 X0 X1
       grind)
    | exact superpose eq27493 eq50721
    | (have j0 := eq50721 X0 X1 x
       grind)
    | exact resolve eq50721 eq27493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27493 eq50721
  have eq51146 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50766 X0 (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op X0 X0)))
       have i₂ := eq3321 X0
       grind)
    | exact superpose eq3321 eq50766
    | exact resolve eq50766 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321 eq50766
  have eq151266 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) ∨ (σ (k (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) X1)) = (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8624 (M.op (M.op X0 X0) X0) (M.op X0 X0) x
       have i₂ := eq1918 X0
       grind)
    | exact superpose eq1918 eq8624
    | exact resolve eq8624 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918 eq8624
  have eq152075 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) X1)) = (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq151266 X0 X1
       have i₂ := eq3112 X0
       grind)
    | exact superpose eq3112 eq151266
    | (have j0 := eq151266 X0 X1
       grind)
    | exact resolve eq151266 eq3112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151266
  have eq152202 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq152075 X0 X1
       have i₂ := eq3112 X0
       grind)
    | exact superpose eq3112 eq152075
    | (have j0 := eq152075 X0 X1
       grind)
    | exact resolve eq152075 eq3112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112 eq152075
  have eq152258 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq152202 X0 X1
       have i₂ := eq3311 X0
       grind)
    | exact superpose eq3311 eq152202
    | (have j0 := eq152202 X0 X1
       grind)
    | exact resolve eq152202 eq3311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311 eq152202
  have eq152522 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq152258 x y
       grind)
    | exact superpose eq152258 eq16
    | (have j1 := eq152258 x y
       grind)
    | exact resolve eq16 eq152258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152258
  have eq154433 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq152522
       have i₂ := eq51146 x y
       grind)
    | exact superpose eq51146 eq152522
    | (have j1 := eq51146 x y
       grind)
    | exact resolve eq152522 eq51146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51146 eq152522
  have eq154442 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq154433
  have eq154511 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq154442
       grind)
    | exact superpose eq154442 eq10
    | exact resolve eq10 eq154442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154442
  have eq154808 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq154511
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq154511
    | exact resolve eq154511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154511
  have eq154809 : x = (M.op y y) := by grind
  clear eq154808
  have eq155134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1090 y
       have i₂ := eq154809
       grind)
    | exact superpose eq154809 eq1090
    | exact resolve eq1090 eq154809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq154809
  have eq155528 : False := by grind
  exact eq155528

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation2653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  clear eq55 eq57
  have eq77 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq87
  have eq177 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq181 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq177 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq185 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq181 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq181 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq195 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       have j1 := eq77 X1 (σ X0)
       grind)
    | (have r₁ := eq185 X0 X0
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq185 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq185
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq195
    | (have j0 := eq195 X0 X1
       grind)
    | exact resolve eq195 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq211 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq203 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq203
    | exact resolve eq203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq203 x y
       grind)
    | exact superpose eq203 eq16
    | exact resolve eq16 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq275 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq211 X0 (τ X1)
       grind)
    | exact superpose eq211 eq18
    | exact resolve eq18 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq211
  have eq288 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq275
    | exact resolve eq275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq294 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq288
    | exact resolve eq288 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq306 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq222
       have i₂ := eq294 x y
       grind)
    | exact superpose eq294 eq222
    | exact resolve eq222 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq294
  have eq307 : False := by grind
  exact eq307

/-- `Equation2656`: `x = ((x ◇ x) ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_y_pyx_pxy_Equation2656 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2656 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2656.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
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
  have eq51 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq52 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
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
  have eq58 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) (M.op X2 X3)) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X0 X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op X0 X0) (M.op X1 X2)) = (k X1 (M.op (M.op X0 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 X0) (M.op X1 X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 X0) (M.op X1 X2))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X2))
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq80
    | exact resolve eq80 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq142 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq125
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq149 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq142
  have eq207 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq57 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq207 eq14
    | exact resolve eq14 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq58 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq57 eq60
    | exact resolve eq60 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq60 X0 X0
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op X0 X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq58
    | exact resolve eq58 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X0 X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq57
    | exact resolve eq57 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op X0 X1) X0)) ∨ (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq369 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X2 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) X2 X3
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X2 X2) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59 X2 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X3 X4
       have i₂ := eq59 (M.op X0 X1) (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X2 X2) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59 X2 (M.op X0 X1) X3 X4
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq59
    | exact resolve eq59 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2))) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)) (M.op X0 X0) X3 X4
       have i₂ := eq59 (M.op X0 X0) X0 X1 X2
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X3 X4))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X2 X3 X4
       have i₂ := eq59 (M.op X0 X1) (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) X0) (M.op X3 X4))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59 (M.op X0 X1) X2 X3 X4
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq59
    | exact resolve eq59 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X2 X2) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X2 X1 (M.op (M.op X0 X0) (M.op x x)) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op x x))
       have i₂ := eq59 X0 X1 x x
       grind)
    | exact superpose eq59 eq60
    | exact resolve eq60 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X2 X3
       have i₂ := eq59 (M.op X0 X1) (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))
       have i₂ := eq59 (M.op X0 X1) (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq59 eq57
    | exact resolve eq57 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq419
    | exact resolve eq419 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq426 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq417 X0 X1 X2 X3
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq417
    | exact resolve eq417 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq430 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X3 X4))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq392 X0 X1 X2 X3 X4
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq392
    | exact resolve eq392 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq431 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq390 X0 X1 X2 X3 X4
       have i₂ := eq60 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)
       grind)
    | exact superpose eq60 eq390
    | exact resolve eq390 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq432 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X2 X2) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq385 X0 X1 X2 X3 X4
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq385
    | exact resolve eq385 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq434 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2)) (M.op (M.op X0 X0) X0)) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq431 X1 X1 X2 X3 X4
       have i₂ := eq60 X1 X1
       grind)
    | exact superpose eq60 eq431
    | exact resolve eq431 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq464 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (k X0 (M.op (M.op X0 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq550 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq68 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq560 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq570 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq550
    | (have j0 := eq550 X0 X1
       grind)
    | exact resolve eq550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq836 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq207 eq208
    | exact resolve eq208 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X2 X2) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq217 X2 (M.op X0 X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq217
    | exact resolve eq217 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1340 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq397 X2 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq397 X0 X0 X0
       grind)
    | exact superpose eq397 eq397
    | exact resolve eq397 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1346 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq207 eq397
    | exact resolve eq397 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1347 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq216 eq397
    | exact resolve eq397 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1396 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq397 X0 X0 X0
       grind)
    | exact superpose eq397 eq14
    | exact resolve eq14 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1398 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op (M.op X0 X0) X0)
       have i₂ := eq397 X0 X0 X0
       grind)
    | exact superpose eq397 eq57
    | exact resolve eq57 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq58 (M.op (M.op X0 X0) X0)
       have i₂ := eq397 X0 X0 X0
       grind)
    | exact superpose eq397 eq58
    | exact resolve eq58 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1406 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq356 (M.op (M.op X0 X0) X0)
       have i₂ := eq397 X0 X0 X0
       grind)
    | exact superpose eq397 eq356
    | exact resolve eq356 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq1409 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq414 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq397 X0 X0 X0
       grind)
    | exact superpose eq397 eq414
    | exact resolve eq414 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1621 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq363 X0
       have i₂ := eq1398 X0
       grind)
    | exact superpose eq1398 eq363
    | exact resolve eq363 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1622 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op x y)) x) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq367 X0 X0
       have i₂ := eq1398 X0
       grind)
    | exact superpose eq1398 eq367
    | exact resolve eq367 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1643 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op X0 (M.op x y)) x)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq214 (M.op X0 X0) X0
       have i₂ := eq1398 X0
       grind)
    | exact superpose eq1398 eq214
    | exact resolve eq214 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1648 : (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x x) x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1398 eq366
    | exact resolve eq366 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1659 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq366 eq1648
    | exact resolve eq1648 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1692 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq57 eq1621
    | exact resolve eq1621 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1733 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq1692 X0
       grind)
    | exact superpose eq1692 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq1692 X0
       grind)
    | exact resolve eq13 eq1692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1759 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1733 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733
  have eq2326 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1406 X0
       have i₂ := eq1398 X0
       grind)
    | exact superpose eq1398 eq1406
    | exact resolve eq1406 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2331 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op x y) X1)) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op x y) X1)) (M.op (M.op X0 X0) (M.op (M.op x y) X1))) (M.op (M.op X0 X0) (M.op (M.op x y) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1406 (M.op (M.op X0 X0) (M.op sF0 x))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1406
    | exact resolve eq1406 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq2363 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op x y) X1)) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op x y) X1)) (M.op x y)) x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2331 X0 X1
       have i₂ := eq1398 (M.op (M.op X0 X0) (M.op sF0 X1))
       grind)
    | exact superpose eq1398 eq2331
    | exact resolve eq2331 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331
  have eq2379 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op x y) X1)) = (M.op (M.op X0 x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2363 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2363
    | exact resolve eq2363 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363
  have eq2514 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1409 X0 X1
       have i₂ := eq1398 X0
       grind)
    | exact superpose eq1398 eq1409
    | exact resolve eq1409 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3647 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq369 (M.op (M.op X0 X1) X2) (M.op X0 X1) X0 X1
       have i₂ := eq369 (M.op X0 X1) X2 (M.op X0 X1) X2
       grind)
    | exact superpose eq369 eq369
    | exact resolve eq369 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4253 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X1 X0 X1
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq369
    | exact resolve eq369 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4257 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq367 (M.op X0 X1) X0
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq367
    | exact resolve eq367 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4455 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = (k (M.op (M.op X0 X1) X0) (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op (M.op X0 X1) (M.op x y)) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq464 (M.op (M.op X0 X1) X0) (M.op X0 X1)
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq464
    | exact resolve eq464 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4545 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = (k (M.op (M.op X0 X1) X0) (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op x y)) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq4455 X1 X1
       have i₂ := eq60 (M.op X1 X1) X1
       grind)
    | exact superpose eq60 eq4455
    | exact resolve eq4455 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455
  have eq4589 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = (k (M.op (M.op X0 X1) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op (M.op (M.op X0 X1) (M.op x y)) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq4545 X0 X1
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq4545
    | exact resolve eq4545 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4545
  have eq4606 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op (M.op X0 X1) (M.op x y))) = (k (M.op (M.op X0 X1) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op (M.op X0 X1) (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4589 X0 X1
       have i₂ := eq60 (M.op (M.op X0 X1) sF0) x
       grind)
    | exact superpose eq60 eq4589
    | exact resolve eq4589 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589
  have eq4611 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq2326 eq4606
    | exact resolve eq4606 eq2326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2326 eq4606
  have eq5625 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X2) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq426 X0 X1 X2 X3
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq426
    | exact resolve eq426 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq5783 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op x y)) x) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5625 (M.op X0 X0) X1 (M.op X1 X1) x
       have i₂ := eq397 x X0 X1
       grind)
    | exact superpose eq397 eq5625
    | exact resolve eq5625 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5792 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op x y)) x) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5625 (M.op X0 X0) (M.op X1 X2) (M.op (M.op X1 X2) X1) (M.op x x)
       have i₂ := eq393 X1 X2 X0 x x
       grind)
    | exact superpose eq393 eq5625
    | exact resolve eq5625 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq5794 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) (M.op x y)) x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5625 (M.op X0 X0) (M.op (M.op X1 X2) X3) X1 X2
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq5625
    | exact resolve eq5625 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5796 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) X2) = (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X3) X4)) (M.op x y)) x) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5625 (M.op X0 X1) (M.op (M.op X2 X3) X4) X2 X3
       have i₂ := eq5625 X0 X1 (M.op X2 X3) X4
       grind)
    | exact superpose eq5625 eq5625
    | exact resolve eq5625 eq5625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5803 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op x y)) x) = (M.op (M.op X0 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5625 (M.op (M.op X0 X1) X0) X2 (M.op X2 X2) (M.op x x)
       have i₂ := eq386 X0 X1 X2 x x
       grind)
    | exact superpose eq386 eq5625
    | exact resolve eq5625 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5847 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (M.op x y)) x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq366 (M.op sF4 x) X1
       have i₂ := eq5625 (M.op sF4 x) X1 sF4 x
       grind)
    | exact superpose eq5625 eq366
    | exact resolve eq366 eq5625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq6027 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op x y)) x) ≠ (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op (M.op X0 X1) (M.op X2 X3))) ∨ (M.op (M.op (M.op X0 X1) (M.op x y)) x) = (k (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq365 (M.op (M.op X0 X1) (M.op X2 X3)) X2
       have i₂ := eq5625 X0 X1 X2 X3
       grind)
    | (have i₁ := eq365 (M.op (M.op X0 X1) (M.op x y)) x
       have i₂ := eq5625 X0 X1 X2 X3
       grind)
    | exact superpose eq5625 eq365
    | (have j0 := eq365 (M.op (M.op X0 X1) (M.op x y)) x
       grind)
    | exact resolve eq365 eq5625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq6149 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op x y)) x) ∨ (M.op (M.op (M.op X0 X1) (M.op x y)) x) = (k (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) := by
    intro X0 X1
    first
    | exact superpose eq2514 eq6027
    | (have j0 := eq6027 X0 X1 x x
       grind)
    | exact resolve eq6027 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514 eq6027
  have eq8544 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op (M.op X0 X1) (M.op X3 X4))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq430 X0 X1 X2 X3 X4
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq430
    | exact resolve eq430 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq8633 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op (M.op X0 X1) x)) (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op x y) X3)) (M.op X4 X5))) = X2 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8544 (M.op (M.op X0 X1) X0) (M.op sF0 X3) X2 X3 X4
       have i₂ := eq369 X0 X1 sF0 X3
       grind)
    | exact superpose eq369 eq8544
    | exact resolve eq8544 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8867 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op x y)) x) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) := by
    intro X0 X1
    first
    | exact superpose eq8544 eq367
    | exact resolve eq367 eq8544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8969 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op x y)) x) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq8867 X0 X1
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq8867
    | exact resolve eq8867 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8867
  have eq9085 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X2 X2) (M.op X3 X4))) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq432 X0 X1 X2 X3 X4
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq432
    | exact resolve eq432 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq9097 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 X1) (M.op (M.op X1 X1) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9085 (M.op (M.op X0 X0) X0) X0 X2 X3 x
       have i₂ := eq363 X0
       grind)
    | exact superpose eq363 eq9085
    | exact resolve eq9085 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9179 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op x y)) x) = (M.op X0 (M.op (M.op X1 X1) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9085 (M.op X0 X0) (M.op X1 X2) X1 X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq9085
    | exact resolve eq9085 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9191 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op x y)) x) = (M.op X0 (M.op (M.op x x) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq9085
    | exact resolve eq9085 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9192 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (M.op x y)) x) = (M.op X0 (M.op (M.op (σ x) (σ x)) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq58 eq9085
    | exact resolve eq9085 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq9364 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X1 (M.op X0 X0) (M.op x x)
       have i₂ := eq9085 X0 X1 X0 x x
       grind)
    | exact superpose eq9085 eq369
    | exact resolve eq369 eq9085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq9444 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op x y)) x) = (M.op (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5625 X2 X3 (M.op (M.op X0 X1) X4) (M.op (M.op X4 X4) (M.op x x))
       have i₂ := eq9085 X0 X1 X4 x x
       grind)
    | exact superpose eq9085 eq5625
    | exact resolve eq5625 eq9085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9085
  have eq9975 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op x y)) x) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X2 X3)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5625 X0 X1 (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X2 X3)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) (M.op x x)
       have i₂ := eq434 (M.op X0 X1) X2 X3 x x
       grind)
    | exact superpose eq434 eq5625
    | exact resolve eq5625 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq5625
  have eq10010 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op x y)) x) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op X2 X3)) (M.op (M.op (M.op X0 X1) (M.op x y)) x))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9975 X0 X1 X2 X3
       have i₂ := eq1398 (M.op X0 X1)
       grind)
    | exact superpose eq1398 eq9975
    | exact resolve eq9975 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9975
  have eq10056 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op x y)) x) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op X2 X3)) (M.op (M.op (M.op X0 X1) (M.op x y)) x))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10010 X0 X1 X2 X3
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq10010
    | exact resolve eq10010 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10010
  have eq11927 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X1))) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X1))) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X1)) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X1))) ∨ (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X1))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 (M.op (M.op X0 X0) (M.op X0 X1))
       have i₂ := eq464 X0 X1
       grind)
    | exact superpose eq464 eq570
    | (have j0 := eq570 X0 (M.op (M.op X0 X0) (M.op X0 X1))
       grind)
    | exact resolve eq570 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq570
  have eq12040 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X1))) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X1))) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11927 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11927
  have eq12751 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) ∨ (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq12752 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) ∨ (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq12751 X0 X1
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq12751
    | (have j0 := eq12751 X0 X1
       grind)
    | exact resolve eq12751 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq12751
  have eq12953 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op x y)) x) = (k (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op X0 X1)) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op x y)) x) := by
    intro X0 X1
    first
    | exact superpose eq8544 eq12752
    | (have j0 := eq12752 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op x y)) x)
       grind)
    | exact resolve eq12752 eq8544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8544 eq12752
  have eq12985 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op x y)) x) = (k (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op X0 X1)) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq12953 X0 X1
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq12953
    | (have j0 := eq12953 X0 X1
       grind)
    | exact resolve eq12953 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12953
  have eq13058 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op x y)) x) ∨ (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op x y)) x) = (k (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12985 X0 X1
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq12985
    | (have j0 := eq12985 X0 X1
       grind)
    | exact resolve eq12985 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12985
  have eq18872 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq207 eq149
    | exact resolve eq149 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq18873 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq207 eq18872
    | exact resolve eq18872 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18872
  have eq21433 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq836 eq386
    | exact resolve eq386 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq836
  have eq21487 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq208 eq21433
    | exact resolve eq21433 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq21433
  have eq21589 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq21487 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq363 X0
       grind)
    | exact superpose eq363 eq21487
    | exact resolve eq21487 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21487
  have eq22963 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1347 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq397 X0 X0 X0
       grind)
    | exact superpose eq397 eq1347
    | exact resolve eq1347 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq23596 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq363 X0
       have i₂ := eq1396 X0 X1 X2
       grind)
    | exact superpose eq1396 eq363
    | exact resolve eq363 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23677 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op x y)) x) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 (M.op X0 X1)
       have i₂ := eq1396 X0 X0 X1
       grind)
    | exact superpose eq1396 eq367
    | exact resolve eq367 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23769 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq367 eq23677
    | exact resolve eq23677 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23677
  have eq24488 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op (M.op (M.op X0 X0) X0) x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4253 X0 (M.op sF0 x)
       have i₂ := eq1396 X0 sF0 x
       grind)
    | exact superpose eq1396 eq4253
    | exact resolve eq4253 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq24856 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X2)) = (M.op X0 (M.op X0 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23596 (M.op X0 (M.op (M.op X0 X1) X2)) X0 X1
       have i₂ := eq23596 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq23596 eq23596
    | exact resolve eq23596 eq23596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24977 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24856 X0 X1 X2
       have i₂ := eq23769 X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq23769 eq24856
    | exact resolve eq24856 eq23769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24856
  have eq31034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq31035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq31034
    | exact resolve eq31034 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31034
  have eq31046 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq31035
       have r₂ := eq28
       grind)
    | exact resolve eq31035 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31035
  have eq31146 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31046 eq23769
    | exact resolve eq23769 eq31046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31046
  have eq31149 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq31146
    | exact resolve eq31146 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31146
  have eq31166 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31149 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq31149
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq31149
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq31149
       grind)
    | exact resolve eq13 eq31149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31149
  have eq31211 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq31166
  have eq31234 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31211 eq56
    | exact resolve eq56 eq31211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq31211
  have eq31255 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq31234
    | exact resolve eq31234 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31234
  have eq31258 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq31255
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq31255
       have r₂ := eq13 x y
       grind)
    | exact resolve eq31255 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31255
  have eq31272 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq31258
       grind)
    | exact superpose eq31258 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq31258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31258
  have eq31273 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31272
  have eq31276 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31273
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31273
    | exact resolve eq31273 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31273
  have eq32155 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1759 x
       have i₂ := eq31276
       grind)
    | exact superpose eq31276 eq1759
    | exact resolve eq1759 eq31276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq32203 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23769 x x
       have i₂ := eq31276
       grind)
    | exact superpose eq31276 eq23769
    | exact resolve eq23769 eq31276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31276
  have eq32208 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32203
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32203
    | exact resolve eq32203 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32203
  have eq32209 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32208
  have eq32221 : x = (k y x) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32155
       have r₂ := eq51
       grind)
    | exact resolve eq32155 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq32155
  have eq32234 : x ≠ x ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq32209
       grind)
    | exact superpose eq32209 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq32209
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq32209
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq32209
       grind)
    | exact resolve eq13 eq32209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32209
  have eq32279 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32234
  have eq32587 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq32279
       grind)
    | exact superpose eq32279 eq45
    | exact resolve eq45 eq32279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32279
  have eq32612 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32587
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32587
    | exact resolve eq32587 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32587
  have eq32845 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32612 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq32612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32612
  have eq32847 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq32845
    | exact resolve eq32845 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32845
  have eq32848 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq32847
  have eq32885 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq88
       have i₂ := eq32221
       grind)
    | exact superpose eq32221 eq88
    | exact resolve eq88 eq32221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32221
  have eq32913 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32885
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32885
    | exact resolve eq32885 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32885
  have eq32918 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq32913
       have r₂ := eq52
       grind)
    | exact resolve eq32913 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32913
  have eq32941 : (τ (σ x)) = (k y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq32918 eq98
    | exact resolve eq98 eq32918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq32918
  have eq32960 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq32941
    | exact resolve eq32941 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32941
  have eq32977 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq32960
       grind)
    | exact superpose eq32960 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32960
  have eq32978 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq32977
  have eq32981 : x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32978
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32978
    | exact resolve eq32978 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32978
  have eq33868 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23769 y y
       have i₂ := eq32981
       grind)
    | exact superpose eq32981 eq23769
    | exact resolve eq23769 eq32981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32981
  have eq33870 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq33868
  have eq33933 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq33870
       grind)
    | exact superpose eq33870 eq14
    | exact resolve eq14 eq33870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33935 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq60 y x
       have i₂ := eq33870
       grind)
    | exact superpose eq33870 eq60
    | exact resolve eq60 eq33870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33960 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4611 y x
       have i₂ := eq33870
       grind)
    | exact superpose eq33870 eq4611
    | exact resolve eq4611 eq33870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4611
  have eq33974 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23596 X0 y x
       have i₂ := eq33870
       grind)
    | exact superpose eq33870 eq23596
    | exact resolve eq23596 eq33870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23596
  have eq33983 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33960
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33960
    | exact resolve eq33960 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33960
  have eq33994 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33935
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33935
    | exact resolve eq33935 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33935
  have eq34052 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33983 eq123
    | exact resolve eq123 eq33983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq33983
  have eq34079 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34052
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34052
    | exact resolve eq34052 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34052
  have eq34785 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X1 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq363 X0
       have i₂ := eq1340 X0 X1 X2
       grind)
    | exact superpose eq1340 eq363
    | exact resolve eq363 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34964 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op x y)) x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4253 (M.op X0 X1) (M.op (M.op X1 X1) x)
       have i₂ := eq1340 X0 X1 x
       grind)
    | exact superpose eq1340 eq4253
    | exact resolve eq4253 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34989 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq367 eq34964
    | exact resolve eq34964 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34964
  have eq35547 : x = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33933 x
       have i₂ := eq33994
       grind)
    | exact superpose eq33994 eq33933
    | exact resolve eq33933 eq33994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33933 eq33994
  have eq35616 : x = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by grind
  clear eq35547
  have eq36733 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33974 y
       have i₂ := eq33870
       grind)
    | exact superpose eq33870 eq33974
    | exact resolve eq33974 eq33870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33870 eq33974
  have eq36821 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq36733
  have eq36864 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36821
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36821
    | exact resolve eq36821 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36821
  have eq36901 : (M.op (M.op x y) x) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36864 eq21589
    | exact resolve eq21589 eq36864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21589
  have eq37190 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36901 eq36864
    | exact resolve eq36864 eq36901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36864 eq36901
  have eq37244 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq37190
  have eq37270 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37244 eq18873
    | exact resolve eq18873 eq37244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18873
  have eq37275 : x = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37244 eq35616
    | exact resolve eq35616 eq37244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35616 eq37244
  have eq37331 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq37275
  have eq37335 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq37270
  have eq37355 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37335
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37335
    | exact resolve eq37335 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37335
  have eq37373 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq37331
  have eq37517 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37373
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37373
    | exact resolve eq37373 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37373
  have eq37531 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37517
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37517
    | exact resolve eq37517 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37517
  have eq37532 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq37531
  have eq37589 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq37532
       grind)
    | exact superpose eq37532 eq88
    | exact resolve eq88 eq37532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq37532
  have eq37615 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq37589
    | exact resolve eq37589 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37589
  have eq55873 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq5783 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq3647 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq3647 eq5783
    | exact resolve eq5783 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55958 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq5783 eq55873
    | exact resolve eq55873 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55873
  have eq56230 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55958 X0 X1
       have i₂ := eq1692 (M.op X0 X1)
       grind)
    | exact superpose eq1692 eq55958
    | exact resolve eq55958 eq1692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692 eq55958
  have eq56263 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56230 X0 X1
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq56230
    | exact resolve eq56230 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56230
  have eq62172 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op (M.op (M.op X0 X0) X0) X2)) (M.op x y)) x) = (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1399 eq5794
    | exact resolve eq5794 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq62227 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op (M.op X0 X1) X0) X3)) = (M.op (M.op (M.op (M.op X2 X2) (M.op (M.op X0 X1) X4)) (M.op x y)) x) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq999 eq5794
    | exact resolve eq5794 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq62490 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = (M.op (M.op (M.op (M.op X2 X2) (M.op (M.op X0 X1) X0)) (M.op x y)) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq4257 eq5794
    | exact resolve eq5794 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4257
  have eq62649 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq5794 eq5783
    | exact resolve eq5783 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62751 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62649 X0 X1 X2 X3
       have i₂ := eq60 (M.op X1 X2) X3
       grind)
    | exact superpose eq60 eq62649
    | exact resolve eq62649 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq62649
  have eq62874 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq5794 eq62490
    | exact resolve eq62490 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62490
  have eq62933 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op (M.op X0 X1) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq5794 eq62227
    | exact resolve eq62227 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62227
  have eq62945 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq5794 eq62172
    | exact resolve eq62172 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62172
  have eq62982 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62751 X0 X1 X2 X3
       have i₂ := eq3647 X1 X2 X3
       grind)
    | exact superpose eq3647 eq62751
    | exact resolve eq62751 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62751
  have eq71222 : ∀ X0 X1 X2 X5 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op (M.op (M.op X1 X1) (M.op (M.op (M.op X0 (M.op x y)) x) X5)) (M.op x y)) x) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq5794 X1 (M.op X0 X2) (M.op (M.op X2 X2) (M.op x x)) X5
       have i₂ := eq9097 X0 X2 x x
       grind)
    | exact superpose eq9097 eq5794
    | exact resolve eq5794 eq9097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9097
  have eq71246 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op X0 (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5794 eq71222
    | exact resolve eq71222 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5794 eq71222
  have eq232872 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x x) (M.op X1 X2))) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5783 eq9191
    | exact resolve eq9191 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9191
  have eq232873 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x x) (M.op X1 X2))) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq207 eq232872
    | exact resolve eq232872 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232872
  have eq233749 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op x y) x)) (M.op x x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x x) (M.op x x)
       have i₂ := eq232873 (M.op X0 X0) x x
       grind)
    | exact superpose eq232873 eq14
    | exact resolve eq14 eq232873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232873
  have eq234702 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (M.op X1 X2))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5783 eq9192
    | exact resolve eq9192 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5783 eq9192
  have eq234703 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (M.op X1 X2))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq216 eq234702
    | exact resolve eq234702 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234702
  have eq235301 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq234703 (M.op (M.op x x) sF2) x x
       have i₂ := eq59 sF2 x x x
       grind)
    | exact superpose eq59 eq234703
    | exact resolve eq234703 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq376475 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op (M.op x y) x) X0)) (M.op X0 X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq1346 X1 (M.op x x)
       have i₂ := eq9179 (M.op (M.op sF0 x) X1) X1 x x x
       grind)
    | exact superpose eq9179 eq1346
    | exact resolve eq1346 eq9179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq376963 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | exact superpose eq5792 eq376475
    | exact resolve eq376475 eq5792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5792 eq376475
  have eq446224 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op x y)) x) = (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5796 X0 X1 X1 X1 x
       have i₂ := eq1340 X0 X1 x
       grind)
    | exact superpose eq1340 eq5796
    | exact resolve eq5796 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq446857 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq367 eq446224
    | exact resolve eq446224 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq446224
  have eq634311 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X1 (M.op (M.op (σ x) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq8633 eq234703
    | exact resolve eq234703 eq8633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8633 eq234703
  have eq1304559 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op x y)) x) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op X2 X3)) (M.op (M.op X0 X1) (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10056 X0 X1 X2 X3
       have i₂ := eq3647 (M.op (M.op X0 X1) sF0) x (M.op X2 X3)
       grind)
    | exact superpose eq3647 eq10056
    | exact resolve eq10056 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10056
  have eq2594944 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op x y)) x) (M.op X0 X1)) ∨ (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op x y)) x) = (k (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq5796 eq13058
    | (have j0 := eq13058 X0 X1
       grind)
    | exact resolve eq13058 eq5796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5796 eq13058
  have eq2594945 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) ∨ (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op x y)) x) = (k (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq4253 eq2594944
    | (have j0 := eq2594944 X0 X1
       grind)
    | exact resolve eq2594944 eq4253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253 eq2594944
  have eq2594946 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) ∨ (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op x y)) x) = (k (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq8969 eq2594945
    | (have j0 := eq2594945 X0 X1
       grind)
    | exact resolve eq2594945 eq8969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594945
  have eq2594947 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op x y)) x) = (k (M.op (M.op (M.op X0 X1) (M.op x y)) x) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) := by
    intro X0 X1
    first
    | exact superpose eq8969 eq2594946
    | (have j0 := eq2594946 X0 X1
       grind)
    | exact resolve eq2594946 eq8969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8969 eq2594946
  have eq2938900 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq235301 X0
       have i₂ := eq71246 sF4 (M.op (M.op X0 X0) sF2) sF2
       grind)
    | exact superpose eq71246 eq235301
    | exact resolve eq235301 eq71246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235301
  have eq3721706 : ∀ X0 : G, (M.op (M.op (M.op X0 x) X0) (M.op x x)) = X0 := by
    intro X0
    first
    | exact superpose eq2379 eq233749
    | exact resolve eq233749 eq2379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379 eq233749
  have eq3891211 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32848 eq23769
    | exact resolve eq23769 eq32848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32848
  have eq3891468 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq3891211
    | exact resolve eq3891211 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891211
  have eq3891469 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3891468
  have eq3892340 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (M.op x y)) x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3891469 eq446857
    | exact resolve eq446857 eq3891469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446857 eq3891469
  have eq3892511 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1621 eq3892340
    | exact resolve eq3892340 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621 eq3892340
  have eq3892906 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3892511
  have eq3894153 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq3892906
    | exact resolve eq3892906 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3892906
  have eq3894379 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq3894153
    | exact resolve eq3894153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3894153
  have eq3894380 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3894379
  have eq3898966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3894380 eq37615
    | exact resolve eq37615 eq3894380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3894380
  have eq3899080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3898966
  have eq3899099 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3899080
       have r₂ := eq28
       grind)
    | exact resolve eq3899080 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3899080
  have eq3899109 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3899099 eq28
    | exact resolve eq28 eq3899099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3899110 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3899099 eq52
    | (have r₁ := eq52
       have r₂ := eq3899099
       grind)
    | exact resolve eq52 eq3899099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq3899099
  have eq3900161 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3899110
  have eq3900251 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3900161 eq37615
    | exact resolve eq37615 eq3900161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37615 eq3900161
  have eq3900368 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq3900251
  have eq3901423 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3900368 eq34079
    | exact resolve eq34079 eq3900368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34079 eq3900368
  have eq3902161 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq3901423
  have eq3906692 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3902161 eq37355
    | exact resolve eq37355 eq3902161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37355 eq3902161
  have eq3906977 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq3906692
  have eq3907048 : y = (M.op x y) := by
    first
    | (have r₁ := eq3906977
       have r₂ := eq3899109
       grind)
    | exact resolve eq3906977 eq3899109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3899109 eq3906977
  have eq3907118 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3907048 eq21
    | exact resolve eq21 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3907121 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) y) x) = X0 := by
    intro X0
    first
    | exact superpose eq3907048 eq57
    | exact resolve eq57 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq3907166 : (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq3907048 eq207
    | exact resolve eq207 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq3907233 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq3907048 eq1659
    | exact resolve eq1659 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq3907836 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3907233
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3907233
    | exact resolve eq3907233 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907233
  have eq3907906 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3907118
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3907118
    | exact resolve eq3907118 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907118
  have eq3907972 : y = (M.op x x) := by
    first
    | exact superpose eq3907048 eq3907836
    | exact resolve eq3907836 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907836
  have eq3908017 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3907906 eq27
    | exact resolve eq27 eq3907906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3908918 : x = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq3721706 x
       have i₂ := eq3907972
       grind)
    | exact superpose eq3907972 eq3721706
    | exact resolve eq3721706 eq3907972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721706
  have eq3908931 : x = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq363 x
       have i₂ := eq3907972
       grind)
    | exact superpose eq3907972 eq363
    | exact resolve eq363 eq3907972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq3908938 : ∀ X0 : G, y = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq414 x x
       have i₂ := eq3907972
       grind)
    | exact superpose eq3907972 eq414
    | exact resolve eq414 eq3907972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3909233 : x = (M.op (M.op y (σ x)) (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    first
    | (have i₁ := eq2938900 x
       have i₂ := eq3907972
       grind)
    | exact superpose eq3907972 eq2938900
    | exact resolve eq2938900 eq3907972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938900
  have eq3909946 : x = (M.op (M.op y (σ x)) (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | exact superpose eq3907048 eq3909233
    | exact resolve eq3909233 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3909233
  have eq3911172 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq3908017 eq34785
    | exact resolve eq34785 eq3908017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3918934 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ x)) X0)) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq634311 X0 X1
       have i₂ := eq71246 sF4 X1 sF2
       grind)
    | exact superpose eq71246 eq634311
    | exact resolve eq634311 eq71246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634311
  have eq3918935 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ x)) X0)) = (M.op X1 (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0 X1
    first
    | exact superpose eq3907048 eq3918934
    | exact resolve eq3918934 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3918934
  have eq3919169 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op (σ x) (σ y)) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3918935 X0 (M.op (M.op x x) sF2)
       have i₂ := eq397 X0 x sF2
       grind)
    | exact superpose eq397 eq3918935
    | exact resolve eq3918935 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq3920154 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3918935 eq34785
    | exact resolve eq34785 eq3918935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34785
  have eq3920326 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (σ x)) (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | exact superpose eq3918935 eq376963
    | exact resolve eq376963 eq3918935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376963 eq3918935
  have eq3922014 : y = (M.op (M.op (M.op y x) (σ x)) (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | exact superpose eq3907048 eq3920326
    | exact resolve eq3920326 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920326
  have eq3947232 : (M.op x (M.op y (σ x))) = (M.op x (M.op (M.op y (σ x)) (M.op y (σ x)))) := by
    first
    | exact superpose eq3909946 eq56263
    | exact resolve eq56263 eq3909946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56263
  have eq3947417 : (M.op x (M.op y (σ x))) = (M.op x (M.op (M.op y (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3947232
       have i₂ := eq62945 (M.op y sF2) x
       grind)
    | exact superpose eq62945 eq3947232
    | exact resolve eq3947232 eq62945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3947232
  have eq3947751 : (M.op x (M.op y (σ x))) = (M.op x (M.op (M.op y (σ x)) (M.op x y))) := by
    first
    | (have i₁ := eq3947417
       have i₂ := eq71246 (M.op y sF2) x sF4
       grind)
    | exact superpose eq71246 eq3947417
    | exact resolve eq3947417 eq71246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3947417
  have eq3947956 : (M.op x (M.op y (σ x))) = (M.op x (M.op (M.op y (σ x)) y)) := by
    first
    | exact superpose eq3907048 eq3947751
    | exact resolve eq3947751 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3947751
  have eq3948089 : y = (M.op x (M.op (M.op y (σ x)) y)) := by
    first
    | (have i₁ := eq3947956
       have i₂ := eq3908938 sF2
       grind)
    | exact superpose eq3908938 eq3947956
    | exact resolve eq3947956 eq3908938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3947956
  have eq3965220 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 (M.op (M.op X0 X0) (σ x))) (M.op (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X1 X2)) (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3919169 eq1304559
    | exact resolve eq1304559 eq3919169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304559 eq3919169
  have eq3965264 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 (M.op (M.op X0 X0) (σ x))) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq3965220 X0 x x
       have i₂ := eq62982 (M.op X0 (M.op (M.op X0 X0) sF2)) (M.op X0 sF0) x (M.op x x)
       grind)
    | exact superpose eq62982 eq3965220
    | exact resolve eq3965220 eq62982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62982 eq3965220
  have eq3965718 : ∀ X0 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 (M.op (M.op X0 X0) (σ x))) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq3907048 eq3965264
    | exact resolve eq3965264 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3965264
  have eq3965972 : ∀ X0 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 X0) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq3965718 X0
       have i₂ := eq414 X0 sF2
       grind)
    | exact superpose eq414 eq3965718
    | exact resolve eq3965718 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq3965718
  have eq3966099 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq3965972 X0
       have i₂ := eq34989 X0 y
       grind)
    | exact superpose eq34989 eq3965972
    | exact resolve eq3965972 eq34989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3965972
  have eq3966651 : (M.op (M.op (M.op x y) x) (M.op (M.op (M.op x y) (σ x)) (M.op (M.op x y) (σ x)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | exact superpose eq3920154 eq9364
    | exact resolve eq9364 eq3920154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9364 eq3920154
  have eq3967849 : (M.op (M.op y (σ x)) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op y x) (M.op (M.op y (σ x)) (M.op y (σ x)))) := by
    first
    | exact superpose eq3907048 eq3966651
    | exact resolve eq3966651 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3966651
  have eq3968362 : (M.op (M.op y (σ x)) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op y x) (M.op (M.op y (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3967849
       have i₂ := eq62945 (M.op y sF2) (M.op y x)
       grind)
    | exact superpose eq62945 eq3967849
    | exact resolve eq3967849 eq62945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3967849
  have eq3968687 : (M.op (M.op y (σ x)) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op y x) (M.op (M.op y (σ x)) (M.op x y))) := by
    first
    | (have i₁ := eq3968362
       have i₂ := eq71246 (M.op y sF2) (M.op y x) sF4
       grind)
    | exact superpose eq71246 eq3968362
    | exact resolve eq3968362 eq71246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968362
  have eq3968853 : (M.op (M.op y x) (M.op (M.op y (σ x)) y)) = (M.op (M.op y (σ x)) (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | exact superpose eq3907048 eq3968687
    | exact resolve eq3968687 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968687
  have eq3968948 : x = (M.op (M.op y x) (M.op (M.op y (σ x)) y)) := by
    first
    | exact superpose eq3909946 eq3968853
    | exact resolve eq3968853 eq3909946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3909946 eq3968853
  have eq3969415 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) x) = (M.op (M.op y (M.op (M.op (M.op X0 X1) (M.op x y)) x)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3922014 eq9444
    | exact resolve eq9444 eq3922014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9444 eq3922014
  have eq3969800 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) x) = (M.op (M.op y X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq62874 eq3969415
    | exact resolve eq3969415 eq62874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62874 eq3969415
  have eq3970107 : ∀ X0 X1 X2 : G, (M.op (M.op y y) y) = (M.op (M.op y X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1398 eq3969800
    | exact resolve eq3969800 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3969800
  have eq3970294 : ∀ X0 X1 X2 : G, (M.op (M.op y x) y) = (M.op (M.op y X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3970107 X0 X1 X2
       have i₂ := eq3907166
       grind)
    | exact superpose eq3907166 eq3970107
    | exact resolve eq3970107 eq3907166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3970107
  have eq3970430 : ∀ X0 X1 X2 : G, x = (M.op (M.op y X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3970294 X0 X1 X2
       have i₂ := eq3908918
       grind)
    | exact superpose eq3908918 eq3970294
    | exact resolve eq3970294 eq3908918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908918 eq3970294
  have eq3977784 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) x) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1409 X0 X1
       have i₂ := eq3966099 X0
       grind)
    | exact superpose eq3966099 eq1409
    | exact resolve eq1409 eq3966099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3979658 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 y)) = (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 y)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62933 (M.op X0 y) x X1 X2
       have i₂ := eq3966099 X0
       grind)
    | exact superpose eq3966099 eq62933
    | exact resolve eq62933 eq3966099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3979791 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op X0 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3979658 X0 X1 X2
       have i₂ := eq1409 X0 y
       grind)
    | exact superpose eq1409 eq3979658
    | exact resolve eq3979658 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq3979658
  have eq3984622 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X0 (M.op (M.op x (M.op y x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq3968948 eq62933
    | exact resolve eq62933 eq3968948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62933
  have eq3984801 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3984622 X0 X1
       have i₂ := eq3908938 x
       grind)
    | exact superpose eq3908938 eq3984622
    | exact resolve eq3984622 eq3908938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908938 eq3984622
  have eq4036489 : ∀ X0 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x y) (M.op (M.op x X0) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq5803 x y (M.op x X0)
       have i₂ := eq3977784 x X0
       grind)
    | exact superpose eq3977784 eq5803
    | exact resolve eq5803 eq3977784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5803 eq3977784
  have eq4037464 : ∀ X0 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x y) (M.op (M.op x X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq4036489 X0
       have i₂ := eq62945 (M.op x X0) (M.op x y)
       grind)
    | exact superpose eq62945 eq4036489
    | exact resolve eq4036489 eq62945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62945 eq4036489
  have eq4038223 : ∀ X0 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x y) (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4037464 X0
       have i₂ := eq71246 (M.op x X0) (M.op x y) sF4
       grind)
    | exact superpose eq71246 eq4037464
    | exact resolve eq4037464 eq71246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71246 eq4037464
  have eq4038594 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | exact superpose eq3907048 eq4038223
    | exact resolve eq4038223 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4038223
  have eq4038758 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq4038594 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4038594
    | (have j0 := eq4038594 X0
       grind)
    | exact resolve eq4038594 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4038594
  have eq4038825 : ∀ X0 : G, (M.op y x) = (M.op y (M.op (M.op x X0) y)) := by
    intro X0
    first
    | exact superpose eq3907048 eq4038758
    | exact resolve eq4038758 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4038758
  have eq4115339 : ∀ X0 X1 : G, (M.op y x) = (M.op y (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4038825 X0
       have i₂ := eq3979791 (M.op x X0) y X1
       grind)
    | (have i₁ := eq4038825 X0
       have i₂ := eq3979791 (M.op x X0) y y
       grind)
    | exact superpose eq3979791 eq4038825
    | exact resolve eq4038825 eq3979791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3979791 eq4038825
  have eq4225608 : ∀ X0 : G, y = (M.op (M.op (M.op y x) (M.op (M.op X0 y) x)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3907048 eq1643
    | exact resolve eq1643 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq4226966 : ∀ X0 : G, (k (M.op (M.op y (M.op x y)) x) y) = (M.op (M.op (M.op (M.op y (M.op x y)) x) (M.op x y)) x) ∨ (M.op (M.op y (M.op x y)) x) = (M.op y (M.op (M.op y x) (M.op (M.op X0 y) x))) := by
    intro X0
    first
    | (have i₁ := eq2594947 (M.op (M.op y x) (M.op (M.op X0 y) x)) (M.op X0 X0)
       have i₂ := eq4225608 X0
       grind)
    | exact superpose eq4225608 eq2594947
    | exact resolve eq2594947 eq4225608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594947 eq4225608
  have eq4226994 : ∀ X0 : G, (M.op y y) = (k (M.op (M.op y (M.op x y)) x) y) ∨ (M.op (M.op y (M.op x y)) x) = (M.op y (M.op (M.op y x) (M.op (M.op X0 y) x))) := by
    intro X0
    first
    | exact superpose eq1622 eq4226966
    | (have j0 := eq4226966 X0
       grind)
    | exact resolve eq4226966 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622 eq4226966
  have eq4227639 : ∀ X0 : G, (M.op y y) = (k (M.op (M.op y y) y) y) ∨ (M.op (M.op y (M.op x y)) x) = (M.op y (M.op (M.op y x) (M.op (M.op X0 y) x))) := by
    intro X0
    first
    | exact superpose eq1398 eq4226994
    | (have j0 := eq4226994 X0
       grind)
    | exact resolve eq4226994 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226994
  have eq4228108 : ∀ X0 : G, (M.op y y) = (k (M.op (M.op y y) x) y) ∨ (M.op (M.op y (M.op x y)) x) = (M.op y (M.op (M.op y x) (M.op (M.op X0 y) x))) := by
    intro X0
    first
    | (have i₁ := eq4227639 X0
       have i₂ := eq3966099 y
       grind)
    | exact superpose eq3966099 eq4227639
    | (have j0 := eq4227639 X0
       grind)
    | exact resolve eq4227639 eq3966099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4227639
  have eq4228443 : ∀ X0 : G, (M.op y x) = (k (M.op (M.op y x) x) y) ∨ (M.op (M.op y (M.op x y)) x) = (M.op y (M.op (M.op y x) (M.op (M.op X0 y) x))) := by
    intro X0
    first
    | (have i₁ := eq4228108 X0
       have i₂ := eq3907166
       grind)
    | exact superpose eq3907166 eq4228108
    | (have j0 := eq4228108 X0
       grind)
    | exact resolve eq4228108 eq3907166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228108
  have eq4228691 : ∀ X0 : G, (k x y) = (M.op y x) ∨ (M.op (M.op y (M.op x y)) x) = (M.op y (M.op (M.op y x) (M.op (M.op X0 y) x))) := by
    intro X0
    first
    | (have i₁ := eq4228443 X0
       have i₂ := eq3908931
       grind)
    | exact superpose eq3908931 eq4228443
    | (have j0 := eq4228443 X0
       grind)
    | exact resolve eq4228443 eq3908931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228443
  have eq4228791 : (M.op y y) = (M.op (M.op y (M.op x y)) x) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq4228691 x
       have i₂ := eq24977 y x (M.op (M.op x y) x)
       grind)
    | exact superpose eq24977 eq4228691
    | exact resolve eq4228691 eq24977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24977 eq4228691
  have eq4228850 : (M.op y y) = (M.op (M.op y y) y) ∨ (k x y) = (M.op y x) := by
    first
    | exact superpose eq1398 eq4228791
    | exact resolve eq4228791 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228791
  have eq4228887 : (M.op y y) = (M.op (M.op y y) x) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq4228850
       have i₂ := eq3966099 y
       grind)
    | exact superpose eq3966099 eq4228850
    | exact resolve eq4228850 eq3966099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228850
  have eq4228912 : (M.op y x) = (M.op (M.op y x) x) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq4228887
       have i₂ := eq3907166
       grind)
    | exact superpose eq3907166 eq4228887
    | exact resolve eq4228887 eq3907166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228887
  have eq4228928 : (k x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4228912
       have i₂ := eq3908931
       grind)
    | exact superpose eq3908931 eq4228912
    | exact resolve eq4228912 eq3908931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228912
  have eq4255161 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) X0)) (M.op x y)) x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3911172 (M.op x x)
       have i₂ := eq9179 sF4 sF1 x x x
       grind)
    | exact superpose eq9179 eq3911172
    | exact resolve eq3911172 eq9179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9179 eq3911172
  have eq4256031 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq5847 eq4255161
    | exact resolve eq4255161 eq5847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5847 eq4255161
  have eq4256315 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq216 eq4256031
    | exact resolve eq4256031 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq4256031
  have eq4324651 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) x) X0) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq3907048 eq24488
    | exact resolve eq24488 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24488
  have eq4327068 : (σ y) = (M.op (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq12040 y x
       have i₂ := eq4324651 (M.op y y) x
       grind)
    | exact superpose eq4324651 eq12040
    | exact resolve eq12040 eq4324651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12040 eq4324651
  have eq4329138 : (σ y) = (M.op (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4327068
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4327068
    | exact resolve eq4327068 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4327068
  have eq4330531 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | exact superpose eq3907906 eq4329138
    | exact resolve eq4329138 eq3907906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4329138
  have eq4331505 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y x))) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4330531
       have i₂ := eq3984801 (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) y
       grind)
    | exact superpose eq3984801 eq4330531
    | exact resolve eq4330531 eq3984801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4330531
  have eq4332232 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) y) x) (M.op y x))) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4331505
       have i₂ := eq3647 y y (M.op y y)
       grind)
    | exact superpose eq3647 eq4331505
    | exact resolve eq4331505 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4331505
  have eq4332727 : (σ (M.op x y)) = (M.op (σ (M.op (M.op y y) (M.op y x))) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4332232
       have i₂ := eq3907121 (M.op y y)
       grind)
    | exact superpose eq3907121 eq4332232
    | exact resolve eq4332232 eq3907121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4332232
  have eq4333083 : (σ (M.op x y)) = (M.op (σ (M.op (M.op y y) y)) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4332727
       have i₂ := eq34989 y x
       grind)
    | exact superpose eq34989 eq4332727
    | exact resolve eq4332727 eq34989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4332727
  have eq4333333 : (σ (M.op x y)) = (M.op (σ (M.op (M.op y y) x)) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4333083
       have i₂ := eq3966099 y
       grind)
    | exact superpose eq3966099 eq4333083
    | exact resolve eq4333083 eq3966099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333083
  have eq4333511 : (σ (M.op x y)) = (M.op (σ (M.op (M.op y x) x)) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4333333
       have i₂ := eq3907166
       grind)
    | exact superpose eq3907166 eq4333333
    | exact resolve eq4333333 eq3907166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333333
  have eq4333648 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4333511
       have i₂ := eq3908931
       grind)
    | exact superpose eq3908931 eq4333511
    | exact resolve eq4333511 eq3908931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333511
  have eq4333755 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4333648
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4333648
    | exact resolve eq4333648 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333648
  have eq4333836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | exact superpose eq3908017 eq4333755
    | exact resolve eq4333755 eq3908017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908017 eq4333755
  have eq4333911 : (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have r₁ := eq4333836
       have r₂ := eq28
       grind)
    | exact resolve eq4333836 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333836
  have eq4333979 : (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y x))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4333911
       have i₂ := eq3984801 (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) y
       grind)
    | exact superpose eq3984801 eq4333911
    | exact resolve eq4333911 eq3984801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333911
  have eq4334024 : (M.op (σ y) (σ y)) = (σ (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) y) x) (M.op y x))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4333979
       have i₂ := eq3647 y y (M.op y y)
       grind)
    | exact superpose eq3647 eq4333979
    | exact resolve eq4333979 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333979
  have eq4334065 : (M.op (σ y) (σ y)) = (σ (M.op (M.op y y) (M.op y x))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4334024
       have i₂ := eq3907121 (M.op y y)
       grind)
    | exact superpose eq3907121 eq4334024
    | exact resolve eq4334024 eq3907121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334024
  have eq4334102 : (M.op (σ y) (σ y)) = (σ (M.op (M.op y y) y)) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4334065
       have i₂ := eq34989 y x
       grind)
    | exact superpose eq34989 eq4334065
    | exact resolve eq4334065 eq34989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334065
  have eq4334134 : (M.op (σ y) (σ y)) = (σ (M.op (M.op y y) x)) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4334102
       have i₂ := eq3966099 y
       grind)
    | exact superpose eq3966099 eq4334102
    | exact resolve eq4334102 eq3966099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334102
  have eq4334155 : (M.op (σ y) (σ y)) = (σ (M.op (M.op y x) x)) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4334134
       have i₂ := eq3907166
       grind)
    | exact superpose eq3907166 eq4334134
    | exact resolve eq4334134 eq3907166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334134
  have eq4334173 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4334155
       have i₂ := eq3908931
       grind)
    | exact superpose eq3908931 eq4334155
    | exact resolve eq4334155 eq3908931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334155
  have eq4334182 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4334173
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4334173
    | exact resolve eq4334173 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334173
  have eq4334190 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | exact superpose eq3907906 eq4334182
    | exact resolve eq4334182 eq3907906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334182
  have eq4334197 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y y)) y)) := by
    first
    | (have i₁ := eq4334190
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4334190
    | exact resolve eq4334190 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334190
  have eq4334203 : (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) (M.op y x)) y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4334197
       have i₂ := eq3984801 (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op y y)) x) y
       grind)
    | exact superpose eq3984801 eq4334197
    | exact resolve eq4334197 eq3984801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3984801 eq4334197
  have eq4334209 : (σ y) = (σ (k (M.op (M.op (M.op (M.op (M.op y y) (M.op y y)) y) x) (M.op y x)) y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4334203
       have i₂ := eq3647 y y (M.op y y)
       grind)
    | exact superpose eq3647 eq4334203
    | exact resolve eq4334203 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3647 eq4334203
  have eq4334215 : (σ y) = (σ (k (M.op (M.op y y) (M.op y x)) y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4334209
       have i₂ := eq3907121 (M.op y y)
       grind)
    | exact superpose eq3907121 eq4334209
    | exact resolve eq4334209 eq3907121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907121 eq4334209
  have eq4334220 : (σ y) = (σ (k (M.op (M.op y y) y) y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4334215
       have i₂ := eq34989 y x
       grind)
    | exact superpose eq34989 eq4334215
    | exact resolve eq4334215 eq34989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34989 eq4334215
  have eq4334225 : (σ y) = (σ (k (M.op (M.op y y) x) y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4334220
       have i₂ := eq3966099 y
       grind)
    | exact superpose eq3966099 eq4334220
    | exact resolve eq4334220 eq3966099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3966099 eq4334220
  have eq4334229 : (σ y) = (σ (k (M.op (M.op y x) x) y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4334225
       have i₂ := eq3907166
       grind)
    | exact superpose eq3907166 eq4334225
    | exact resolve eq4334225 eq3907166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907166 eq4334225
  have eq4334232 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4334229
       have i₂ := eq3908931
       grind)
    | exact superpose eq3908931 eq4334229
    | exact resolve eq4334229 eq3908931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908931 eq4334229
  have eq4334235 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4334232
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq4334232
    | exact resolve eq4334232 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4334232
  have eq4334238 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3907906 eq4334235
    | exact resolve eq4334235 eq3907906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334235
  have eq4334240 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4334238
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4334238
    | exact resolve eq4334238 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334238
  have eq4334242 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3907906 eq4334240
    | exact resolve eq4334240 eq3907906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334240
  have eq4334909 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq4334242 eq23769
    | exact resolve eq23769 eq4334242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334242
  have eq4335128 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq4334909
       have r₂ := eq13 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq4334909 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334909
  have eq4336565 : (τ (σ (M.op x y))) = (k x (M.op x y)) := by
    first
    | exact superpose eq4335128 eq65
    | exact resolve eq65 eq4335128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq4335128
  have eq4336664 : (τ (σ (M.op x y))) = (k x y) := by
    first
    | exact superpose eq3907048 eq4336565
    | exact resolve eq4336565 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4336565
  have eq4336686 : (M.op x y) = (k x y) := by
    first
    | exact superpose eq31 eq4336664
    | exact resolve eq4336664 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4336664
  have eq4336696 : y = (k x y) := by
    first
    | exact superpose eq3907048 eq4336686
    | exact resolve eq4336686 eq3907048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907048 eq4336686
  have eq4336707 : y = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4336696
       have i₂ := eq4228928
       grind)
    | exact superpose eq4228928 eq4336696
    | exact resolve eq4336696 eq4228928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228928 eq4336696
  have eq4361619 : ∀ X0 X1 : G, x = (M.op y (M.op (M.op x X0) X1)) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq3970430 x X0 X1
       have i₂ := eq4336707
       grind)
    | exact superpose eq4336707 eq3970430
    | exact resolve eq3970430 eq4336707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3970430 eq4336707
  have eq4362336 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4361619 x x
       have i₂ := eq4115339 x x
       grind)
    | exact superpose eq4115339 eq4361619
    | exact resolve eq4361619 eq4115339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115339 eq4361619
  have eq4362337 : x = (M.op y x) := by grind
  clear eq4362336
  have eq4363133 : x = (M.op x (M.op (M.op y (σ x)) y)) := by
    first
    | (have i₁ := eq3968948
       have i₂ := eq4362337
       grind)
    | exact superpose eq4362337 eq3968948
    | exact resolve eq3968948 eq4362337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968948
  have eq4363492 : x ≠ (M.op (M.op x (M.op x y)) x) ∨ (M.op (M.op x (M.op x y)) x) = (k (M.op (M.op x (M.op x y)) x) (M.op (M.op x (M.op x y)) x)) := by
    first
    | (have i₁ := eq6149 y x
       have i₂ := eq4362337
       grind)
    | exact superpose eq4362337 eq6149
    | exact resolve eq6149 eq4362337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6149
  have eq4364046 : x ≠ (M.op (M.op x x) x) ∨ (M.op (M.op x (M.op x y)) x) = (k (M.op (M.op x (M.op x y)) x) (M.op (M.op x (M.op x y)) x)) := by
    first
    | exact superpose eq1398 eq4363492
    | exact resolve eq4363492 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363492
  have eq4364160 : x = y := by
    first
    | exact superpose eq3948089 eq4363133
    | exact resolve eq4363133 eq3948089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948089 eq4363133
  have eq4364339 : x ≠ (M.op y x) ∨ (M.op (M.op x (M.op x y)) x) = (k (M.op (M.op x (M.op x y)) x) (M.op (M.op x (M.op x y)) x)) := by
    first
    | (have i₁ := eq4364046
       have i₂ := eq3907972
       grind)
    | exact superpose eq3907972 eq4364046
    | exact resolve eq4364046 eq3907972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364046
  have eq4364516 : (M.op (M.op x (M.op x y)) x) = (k (M.op (M.op x (M.op x y)) x) (M.op (M.op x (M.op x y)) x)) := by
    first
    | (have r₁ := eq4364339
       have r₂ := eq4362337
       grind)
    | exact resolve eq4364339 eq4362337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364339
  have eq4364622 : (M.op (M.op x x) x) = (k (M.op (M.op x x) x) (M.op (M.op x x) x)) := by
    first
    | exact superpose eq1398 eq4364516
    | exact resolve eq4364516 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398 eq4364516
  have eq4364688 : (M.op y x) = (k (M.op y x) (M.op y x)) := by
    first
    | (have i₁ := eq4364622
       have i₂ := eq3907972
       grind)
    | exact superpose eq3907972 eq4364622
    | exact resolve eq4364622 eq3907972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907972 eq4364622
  have eq4364731 : x = (k x x) := by
    first
    | (have i₁ := eq4364688
       have i₂ := eq4362337
       grind)
    | exact superpose eq4362337 eq4364688
    | exact resolve eq4364688 eq4362337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4362337 eq4364688
  have eq4364854 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq4364160
       grind)
    | exact superpose eq4364160 eq25
    | exact resolve eq25 eq4364160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4364160
  have eq4368540 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3907906 eq4364854
    | exact resolve eq4364854 eq3907906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907906 eq4364854
  have eq4369959 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4368540
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4368540
    | exact resolve eq4368540 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4368540
  have eq4373491 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq560 x
       have i₂ := eq4364731
       grind)
    | exact superpose eq4364731 eq560
    | (have j0 := eq560 x
       grind)
    | exact resolve eq560 eq4364731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq4364731
  have eq4373711 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4373491
  have eq4373848 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4373711
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4373711
    | exact resolve eq4373711 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4373711
  have eq4373998 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4369959 eq4373848
    | exact resolve eq4373848 eq4369959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4373848
  have eq4375821 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq4373998 eq22963
    | exact resolve eq22963 eq4373998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22963
  have eq4376675 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq4256315 eq4375821
    | exact resolve eq4375821 eq4256315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4256315 eq4375821
  have eq4377132 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq4369959 eq4376675
    | exact resolve eq4376675 eq4369959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4369959 eq4376675
  have eq4377477 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4377132 x
       have i₂ := eq23769 sF1 x
       grind)
    | exact superpose eq23769 eq4377132
    | exact resolve eq4377132 eq23769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23769 eq4377132
  have eq4377744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4373998 eq4377477
    | exact resolve eq4377477 eq4373998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4373998 eq4377477
  have eq4377956 : False := by grind
  exact eq4377956

/-- `Equation2656`: `x = ((x ◇ x) ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_y_pyx_pxy_Equation2656 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2656 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2656.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
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
  have eq47 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) (M.op X2 X3)) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X0 X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq66 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq67 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq66
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67
    | exact resolve eq67 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq71
    | exact resolve eq71 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq154 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq116
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq162 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq154
  have eq207 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq47 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq47 eq14
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X0 X1)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq48
    | exact resolve eq48 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X2 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) X2 X3
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq394 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X2 X2) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X2 (M.op X0 X1) X3 X4
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X2 X2) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X2 X1 (M.op (M.op X0 X0) (M.op x x)) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op x x))
       have i₂ := eq49 X0 X1 x x
       grind)
    | exact superpose eq49 eq50
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (σ X0)) (M.op (σ (k X0 X0)) (M.op X2 X3))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 (σ X0) X1 X2 X3
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq49
    | (have j1 := eq63 X0 X0
       grind)
    | exact resolve eq49 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq631 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq637 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (σ X0)) (M.op (σ (k X0 X0)) (M.op X2 X3))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq624 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq1084 : (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq209 eq47
    | exact resolve eq47 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1108 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq207 eq1084
    | exact resolve eq1084 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1596 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq405 X2 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq405 X0 X0 X0
       grind)
    | exact superpose eq405 eq405
    | exact resolve eq405 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1617 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq209 eq405
    | exact resolve eq405 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1647 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op (M.op X0 X0) X0)
       have i₂ := eq405 X0 X0 X0
       grind)
    | exact superpose eq405 eq47
    | exact resolve eq47 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1648 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48 (M.op (M.op X0 X0) X0)
       have i₂ := eq405 X0 X0 X0
       grind)
    | exact superpose eq405 eq48
    | exact resolve eq48 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1658 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq427 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq405 X0 X0 X0
       grind)
    | exact superpose eq405 eq427
    | exact resolve eq427 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq1683 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op x y) x) (M.op x y))) (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq207 eq1617
    | exact resolve eq1617 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq1700 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op x y) x) x)) (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1108 eq1683
    | exact resolve eq1683 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq1683
  have eq1859 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq1647 X0
       grind)
    | exact superpose eq1647 eq371
    | exact resolve eq371 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq1888 : (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x x) x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1647 eq372
    | exact resolve eq372 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1900 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq372 eq1888
    | exact resolve eq1888 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1935 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq47 eq1859
    | exact resolve eq1859 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq1859
  have eq2099 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1648 eq372
    | exact resolve eq372 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq2111 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq372 eq2099
    | exact resolve eq2099 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq2099
  have eq4999 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) (M.op (M.op x y) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq209 eq394
    | exact resolve eq394 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq394
  have eq5144 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op x y) (M.op x y)) x)) (M.op (M.op x y) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4999 X0 X1 X2 X3
       have i₂ := eq1647 sF0
       grind)
    | exact superpose eq1647 eq4999
    | exact resolve eq4999 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647 eq4999
  have eq5242 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op x y) x) x)) (M.op (M.op x y) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq207 eq5144
    | exact resolve eq5144 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5144
  have eq7671 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ y) (σ X0)
       have j1 := eq93 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ X0)
       have r₂ := eq93 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq93 y
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq7694 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq7671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7671
  have eq7699 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7694 X0
       have j1 := eq12 (σ y) (σ X0)
       grind)
    | (have r₁ := eq7694 y
       have r₂ := eq12 (σ y) (σ y)
       grind)
    | (have r₁ := eq7694 X0
       have r₂ := eq12 (σ y) (σ X0)
       grind)
    | exact resolve eq7694 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7694
  have eq7718 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq7699
    | (have j0 := eq7699 X0
       grind)
    | exact resolve eq7699 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq7699
  have eq11141 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq374 (σ X0) (σ X0) (σ (k X0 X0)) (M.op x x)
       have i₂ := eq637 X0 (σ X0) x x
       grind)
    | exact superpose eq637 eq374
    | (have j1 := eq637 X0 x x x
       grind)
    | exact resolve eq374 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq637
  have eq17328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq73 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq17329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17328
    | exact resolve eq17328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17328
  have eq17340 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17329
       have r₂ := eq28
       grind)
    | exact resolve eq17329 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17329
  have eq17342 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17340
    | exact resolve eq17340 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17340
  have eq17345 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq17342
  have eq17441 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17345 eq58
    | exact resolve eq58 eq17345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq17345
  have eq17466 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq17441
    | exact resolve eq17441 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17441
  have eq20012 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq17466
       grind)
    | exact superpose eq17466 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq17466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17466
  have eq20013 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20012
  have eq20017 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20013
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20013
    | exact resolve eq20013 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20013
  have eq20018 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20017
  have eq20178 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq20206 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1935 y
       have i₂ := eq20018
       grind)
    | exact superpose eq20018 eq1935
    | exact resolve eq1935 eq20018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20213 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 y y
       have i₂ := eq20018
       grind)
    | exact superpose eq20018 eq50
    | exact resolve eq50 eq20018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20018
  have eq20256 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20213
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20213
    | exact resolve eq20213 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20213
  have eq20290 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq631 x y
       have i₂ := eq20178
       grind)
    | exact superpose eq20178 eq631
    | (have j0 := eq631 x y
       grind)
    | exact resolve eq631 eq20178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq20178
  have eq20293 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20290
  have eq20296 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20293
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20293
    | exact resolve eq20293 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20293
  have eq20307 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20296
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20296
    | exact resolve eq20296 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20296
  have eq20311 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq20307
    | exact resolve eq20307 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20307
  have eq20312 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20311
  have eq20316 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20312
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20312
    | exact resolve eq20312 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20312
  have eq20320 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20316
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20316
    | exact resolve eq20316 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20316
  have eq20329 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq207 eq162
    | exact resolve eq162 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq20330 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq207 eq20329
    | exact resolve eq20329 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq20329
  have eq20331 : x ≠ x ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq20206
       grind)
    | exact superpose eq20206 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20206
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20206
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20206
       grind)
    | exact resolve eq12 eq20206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20206
  have eq20364 : y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20331
  have eq20378 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20364
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20364
    | exact resolve eq20364 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20364
  have eq20706 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20320 eq1935
    | exact resolve eq1935 eq20320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20713 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20320 eq50
    | exact resolve eq50 eq20320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20320
  have eq20752 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq20713
    | exact resolve eq20713 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20713
  have eq20846 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20706 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq20706
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20706
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20706
       grind)
    | exact resolve eq12 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20706
  have eq20879 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20846
  have eq20890 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq20879
    | exact resolve eq20879 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20879
  have eq146664 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq20378
       grind)
    | exact superpose eq20378 eq90
    | exact resolve eq90 eq20378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20378
  have eq146702 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq146664
    | exact resolve eq146664 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146664
  have eq158609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20890 eq146702
    | exact resolve eq146702 eq20890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20890 eq146702
  have eq158620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq158609
  have eq158624 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq158620
       have r₂ := eq28
       grind)
    | exact resolve eq158620 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158620
  have eq161228 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq158624 eq20752
    | exact resolve eq20752 eq158624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20752 eq158624
  have eq161438 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq161228
  have eq161478 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20256
       have i₂ := eq161438
       grind)
    | exact superpose eq161438 eq20256
    | exact resolve eq20256 eq161438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20256 eq161438
  have eq161708 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq161478
  have eq161758 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq161708 eq28
    | exact resolve eq28 eq161708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161799 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq161708 eq2111
    | exact resolve eq2111 eq161708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq161811 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq161799
    | exact resolve eq161799 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161799
  have eq162466 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq161811
  have eq162702 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq161708 eq162466
    | exact resolve eq162466 eq161708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161708 eq162466
  have eq162713 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq162702
  have eq163337 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq162713 eq100
    | exact resolve eq100 eq162713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq163374 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq163337
    | exact resolve eq163337 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq163337
  have eq163398 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq163374
       grind)
    | exact superpose eq163374 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq163374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163374
  have eq163399 : y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq163398
  have eq289429 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1935 x
       have i₂ := eq163399
       grind)
    | exact superpose eq163399 eq1935
    | exact resolve eq1935 eq163399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163399
  have eq289693 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq289429
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq289429
    | exact resolve eq289429 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289429
  have eq289694 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq289693
  have eq289754 : x ≠ x ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq289694
       grind)
    | exact superpose eq289694 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq289694
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq289694
       grind)
    | exact resolve eq12 eq289694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289757 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 y x
       have i₂ := eq289694
       grind)
    | exact superpose eq289694 eq50
    | exact resolve eq50 eq289694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq289764 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq375 y x
       have i₂ := eq289694
       grind)
    | exact superpose eq289694 eq375
    | exact resolve eq375 eq289694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq289784 : ∀ X0 : G, (M.op (M.op y y) y) = (M.op x (M.op (M.op x x) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1596 y x X0
       have i₂ := eq289694
       grind)
    | exact superpose eq289694 eq1596
    | exact resolve eq1596 eq289694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596 eq289694
  have eq289878 : y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq289754
  have eq289947 : (M.op x x) = (M.op (M.op y y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq289784 x
       have i₂ := eq427 x x
       grind)
    | exact superpose eq427 eq289784
    | exact resolve eq289784 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq289784
  have eq289961 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq289764
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq289764
    | exact resolve eq289764 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289764
  have eq289965 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq289757
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq289757
    | exact resolve eq289757 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289757
  have eq289966 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq289878
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq289878
    | exact resolve eq289878 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289878
  have eq290002 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq289961 eq114
    | exact resolve eq114 eq289961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq289961
  have eq290048 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq290002
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq290002
    | exact resolve eq290002 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290002
  have eq305947 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op (M.op x x) (M.op (M.op (M.op x y) x) x)) (M.op (M.op x y) (M.op X0 X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq5242 y y X0 X1
       have i₂ := eq289947
       grind)
    | exact superpose eq289947 eq5242
    | exact resolve eq5242 eq289947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5242 eq289947
  have eq306169 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1700 eq305947
    | exact resolve eq305947 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700 eq305947
  have eq307958 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1658 y y
       have i₂ := eq306169
       grind)
    | exact superpose eq306169 eq1658
    | exact resolve eq1658 eq306169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658 eq306169
  have eq308126 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq307958
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq307958
    | exact resolve eq307958 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307958
  have eq312501 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq308126 eq20330
    | exact resolve eq20330 eq308126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20330 eq308126
  have eq312719 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq312501
  have eq312766 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq312719
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq312719
    | exact resolve eq312719 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312719
  have eq505860 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq289966
       grind)
    | exact superpose eq289966 eq90
    | exact resolve eq90 eq289966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq289966
  have eq505923 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq505860
    | exact resolve eq505860 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505860
  have eq1137970 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq505923 eq162713
    | exact resolve eq162713 eq505923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162713 eq505923
  have eq1138018 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1137970
  have eq1138070 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq289965
       have i₂ := eq1138018
       grind)
    | exact superpose eq1138018 eq289965
    | exact resolve eq289965 eq1138018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289965 eq1138018
  have eq1138701 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1138070
  have eq1139432 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1138701 eq290048
    | exact resolve eq290048 eq1138701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290048 eq1138701
  have eq1139642 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq1139432
  have eq1147686 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1139642 eq312766
    | exact resolve eq312766 eq1139642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312766 eq1139642
  have eq1147840 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1147686
  have eq1147864 : y = (M.op x y) := by
    first
    | (have r₁ := eq1147840
       have r₂ := eq161758
       grind)
    | exact resolve eq1147840 eq161758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161758 eq1147840
  have eq1147881 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1147864 eq21
    | exact resolve eq21 eq1147864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1147991 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1147864 eq1900
    | exact resolve eq1900 eq1147864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq1148587 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1147991
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1147991
    | exact resolve eq1147991 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1147991
  have eq1148654 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1147881
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1147881
    | exact resolve eq1147881 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147881
  have eq1148662 : y = (M.op x x) := by
    first
    | exact superpose eq1147864 eq1148587
    | exact resolve eq1148587 eq1147864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148587
  have eq1149676 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1148654 eq27
    | exact resolve eq27 eq1148654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1150344 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq1148662
       grind)
    | exact superpose eq1148662 eq70
    | exact resolve eq70 eq1148662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1150449 : x = (k y x) := by grind
  clear eq1148662
  have eq1151318 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1150344
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1150344
    | exact resolve eq1150344 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150344
  have eq1151412 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq1148654 eq1151318
    | exact resolve eq1151318 eq1148654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151318
  have eq1152082 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7718 x
       have i₂ := eq1150449
       grind)
    | exact superpose eq1150449 eq7718
    | (have j0 := eq7718 x
       grind)
    | exact resolve eq7718 eq1150449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7718 eq1150449
  have eq1152121 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1152082
  have eq1152155 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1148654 eq1152121
    | exact resolve eq1152121 eq1148654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152121
  have eq1152206 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1152155
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1152155
    | exact resolve eq1152155 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152155
  have eq1152257 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1149676 eq1152206
    | exact resolve eq1152206 eq1149676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152206
  have eq1152297 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1152257
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1152257
    | exact resolve eq1152257 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152257
  have eq1152332 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1148654 eq1152297
    | exact resolve eq1152297 eq1148654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152297
  have eq1166778 : (τ (σ (M.op x y))) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1151412 eq54
    | exact resolve eq54 eq1151412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1167001 : (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq1166778
    | exact resolve eq1166778 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1166778
  have eq1167020 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq1147864 eq1167001
    | exact resolve eq1167001 eq1147864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147864 eq1167001
  have eq1168827 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1152332 eq1935
    | exact resolve eq1935 eq1152332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935 eq1152332
  have eq1169593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1149676 eq1168827
    | exact resolve eq1168827 eq1149676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149676 eq1168827
  have eq1169696 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1169593
       have r₂ := eq28
       grind)
    | exact resolve eq1169593 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169593
  have eq1169755 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1169696 eq28
    | exact resolve eq28 eq1169696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1175168 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11141 x
       have i₂ := eq1167020
       grind)
    | exact superpose eq1167020 eq11141
    | (have j0 := eq11141 x
       grind)
    | exact resolve eq11141 eq1167020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11141 eq1167020
  have eq1175234 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1175168
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1175168
    | exact resolve eq1175168 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175168
  have eq1175375 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1175234
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1175234
    | exact resolve eq1175234 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175234
  have eq1175516 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq1175375
    | exact resolve eq1175375 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1175375
  have eq1175640 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq1169696 eq1175516
    | exact resolve eq1175516 eq1169696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169696 eq1175516
  have eq1175753 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1175640
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1175640
    | exact resolve eq1175640 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175640
  have eq1175754 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq1175753
  have eq1178167 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
  clear eq1175754
  have eq1179230 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1178167 eq1151412
    | exact resolve eq1151412 eq1178167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151412 eq1178167
  have eq1179373 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq1179230
  have eq1179434 : x = y := by
    first
    | (have r₁ := eq1179373
       have r₂ := eq1169755
       grind)
    | exact resolve eq1179373 eq1169755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179373
  have eq1179563 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1179434
       grind)
    | exact superpose eq1179434 eq25
    | exact resolve eq25 eq1179434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1179434
  have eq1181044 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1148654 eq1179563
    | exact resolve eq1179563 eq1148654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148654 eq1179563
  have eq1181603 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1181044
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1181044
    | exact resolve eq1181044 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1181044
  have eq1181913 : False := by grind
  exact eq1181913

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyy_pxy_pyy_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq56 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq58 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq58 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq58 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq111 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq59 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq59
    | (have j0 := eq59 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq59 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq59 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq118 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq118 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq123 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq20 X1
       grind)
    | exact superpose eq20 eq121
    | (have j0 := eq121 X0 X1
       grind)
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq121
  have eq148 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq152 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       have j1 := eq123 X0 X1
       grind)
    | (have r₁ := eq148 X0 X1
       have r₂ := eq123 X0 X1
       grind)
    | (have r₁ := eq148 X0 X0
       have r₂ := eq123 X0 X0
       grind)
    | exact resolve eq148 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq148
  have eq472 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq152 (σ X0) (σ X1)
       grind)
    | exact superpose eq152 eq15
    | exact resolve eq15 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq472 X0 X1
       have i₂ := eq152 X0 X1
       grind)
    | exact superpose eq152 eq472
    | exact resolve eq472 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq472
  have eq482 : False := by grind
  exact eq482

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_y_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  clear eq35
  have eq60 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq74 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) := by
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
  have eq75 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq83
    | (have j0 := eq83 (σ X0) (σ X1)
       grind)
    | exact resolve eq83 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq44
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq44 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq122
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq125
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq125
    | exact resolve eq125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq83
    | (have j0 := eq83 (σ x) (σ y)
       grind)
    | exact resolve eq83 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq193
    | exact resolve eq193 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq197 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq194
       have r₂ := eq27
       grind)
    | exact resolve eq194 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq199 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq197
    | exact resolve eq197 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq201 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq27
    | exact resolve eq27 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq75
    | (have r₁ := eq75
       have r₂ := eq199
       grind)
    | exact resolve eq75 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq199
  have eq347 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq346
  have eq350 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq347 eq126
    | exact resolve eq126 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq354 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq350
  have eq359 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq354
       have r₂ := eq201
       grind)
    | exact resolve eq354 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq354
  have eq365 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq359 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq368 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq365 X0
       have j1 := eq83 X0 (σ y)
       grind)
    | (have r₁ := eq365 X0
       have r₂ := eq83 X0 (σ y)
       grind)
    | exact resolve eq365 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq368 eq126
    | exact resolve eq126 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq368
  have eq400 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq397
  have eq405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq400
    | exact resolve eq400 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq407 : y = (M.op x y) := by
    first
    | (have r₁ := eq405
       have r₂ := eq27
       grind)
    | exact resolve eq405 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq410 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq407 eq20
    | exact resolve eq20 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq407 eq74
    | (have r₁ := eq74
       have r₂ := eq407
       grind)
    | exact resolve eq74 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq418 : y = (M.op y y) ∨ y = (k x y) := by grind
  clear eq413
  have eq424 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq410
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq410
    | exact resolve eq410 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq427 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq424 eq26
    | exact resolve eq26 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq520 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq106
    | (have j0 := eq106 X0 (M.op x y)
       grind)
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq106
  have eq535 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq407 eq520
    | (have j0 := eq520 X0
       grind)
    | exact resolve eq520 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq647 : (σ (k x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq535 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq535
    | (have j0 := eq535 x
       grind)
    | exact resolve eq535 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq535
  have eq660 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq427 eq647
    | exact resolve eq647 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq674 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq660
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq660
    | exact resolve eq660 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq660
  have eq683 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq424 eq674
    | exact resolve eq674 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq427 eq683
    | exact resolve eq683 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq683
  have eq691 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq688
       have r₂ := eq27
       grind)
    | exact resolve eq688 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq697 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq691 eq60
    | exact resolve eq60 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq691
  have eq699 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq407 eq697
    | exact resolve eq697 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq713 : y = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq418
       have i₂ := eq699
       grind)
    | exact superpose eq699 eq418
    | exact resolve eq418 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq791 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (k X0 y) = (M.op X0 y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq713
       grind)
    | exact superpose eq713 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq795 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq791 X0
       have j1 := eq83 X0 y
       grind)
    | (have r₁ := eq791 X0
       have r₂ := eq83 X0 y
       grind)
    | exact resolve eq791 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq791
  have eq843 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq699
       have i₂ := eq795 x
       grind)
    | exact superpose eq795 eq699
    | exact resolve eq699 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq795
  have eq854 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq843
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq843
    | exact resolve eq843 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq843
  have eq859 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq407 eq854
    | exact resolve eq854 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq854
  have eq860 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq859
  have eq871 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq860 eq15
    | exact resolve eq15 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq872 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq871
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq871
    | exact resolve eq871 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq871
  have eq873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq424 eq872
    | exact resolve eq872 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq872
  have eq874 : False := by grind
  exact eq874

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyx_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq194 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq201 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq208 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq196 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq210 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq201 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq201 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq201 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq224 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq208
    | (have j0 := eq208 X0 X1
       grind)
    | exact resolve eq208 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq225 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq226 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq210
    | (have j0 := eq210 X0 X1
       grind)
    | exact resolve eq210 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq227 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq227 X0 X1
       have j1 := eq225 X0 X1
       grind)
    | (have r₁ := eq227 X0 X1
       have r₂ := eq225 X0 X1
       grind)
    | exact resolve eq227 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq227
  have eq236 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq235
    | exact resolve eq235 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq235 x y
       grind)
    | exact superpose eq235 eq16
    | exact resolve eq16 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq327 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq236 X0 (τ X1)
       grind)
    | exact superpose eq236 eq18
    | exact resolve eq18 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq236
  have eq341 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq327
    | exact resolve eq327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq347 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq341
    | exact resolve eq341 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq359 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq248
       have i₂ := eq347 x y
       grind)
    | exact superpose eq347 eq248
    | exact resolve eq248 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq347
  have eq360 : False := by grind
  exact eq360
