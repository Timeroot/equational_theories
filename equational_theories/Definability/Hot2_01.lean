import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1705`: `x = (y ◇ x) ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxy_pyx_Equation1705 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1705 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1705.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X1) X0)) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op y X0) (M.op (M.op x y) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X0 X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X2 X0)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq219 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq393 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op X0 X3) X4) (M.op X3 X4)) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq56 X3 (M.op x X0) (M.op (M.op x x) X0) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq666 : y = (M.op (M.op (M.op (M.op x y) x) y) (M.op x y)) := by
    first
    | (have i₁ := eq219 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq219
    | (have j0 := eq219 x y
       grind)
    | exact resolve eq219 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : (σ y) = (M.op (M.op (M.op (M.op x y) (σ x)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq219
    | (have j0 := eq219 (σ x) (σ y)
       grind)
    | exact resolve eq219 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq684 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq666 eq14
    | exact resolve eq14 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq842 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq868 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq668 eq14
    | exact resolve eq14 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq1128 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq684 eq393
    | exact resolve eq393 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq1132 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq868 eq393
    | exact resolve eq393 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq868
  have eq17432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17432
    | exact resolve eq17432 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17432
  have eq17444 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17433
       have r₂ := eq28
       grind)
    | exact resolve eq17433 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17433
  have eq17446 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17444
    | exact resolve eq17444 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17444
  have eq17453 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq17446
  have eq17508 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17453
    | exact resolve eq17453 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17453
  have eq17927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17508 eq98
    | exact resolve eq98 eq17508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17508
  have eq17940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17927
  have eq17942 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17940
       have r₂ := eq28
       grind)
    | exact resolve eq17940 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17940
  have eq18754 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17942
  have eq18809 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18754
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18754
    | exact resolve eq18754 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18754
  have eq18934 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq18809
       grind)
    | exact superpose eq18809 eq73
    | exact resolve eq73 eq18809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18809
  have eq18960 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18934
    | exact resolve eq18934 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18934
  have eq19299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18960 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq18960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq19299
    | exact resolve eq19299 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19299
  have eq19319 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19308
       have r₂ := eq28
       grind)
    | exact resolve eq19308 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19308
  have eq19321 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq19319
    | exact resolve eq19319 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19319
  have eq19322 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19321
  have eq19330 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19322
  have eq19385 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq19330
    | exact resolve eq19330 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19330
  have eq19811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19385 eq18960
    | exact resolve eq18960 eq19385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18960 eq19385
  have eq19819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19811
  have eq19823 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19819
       have r₂ := eq28
       grind)
    | exact resolve eq19819 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19819
  have eq20079 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19823 eq1132
    | exact resolve eq1132 eq19823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq20086 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20079
    | exact resolve eq20079 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20079
  have eq20534 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19823 eq20086
    | exact resolve eq20086 eq19823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19823 eq20086
  have eq20591 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20534
  have eq20671 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20591
  have eq20729 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20671
    | exact resolve eq20671 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20671
  have eq21664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20729 eq98
    | exact resolve eq98 eq20729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq21681 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq21664
  have eq21684 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21681
       have r₂ := eq28
       grind)
    | exact resolve eq21681 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21681
  have eq21692 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq21684
  have eq21750 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21692
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21692
    | exact resolve eq21692 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21692
  have eq21909 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq21750
       grind)
    | exact superpose eq21750 eq73
    | exact resolve eq73 eq21750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21750
  have eq21937 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq21909
    | exact resolve eq21909 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21909
  have eq21978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21937 eq20729
    | exact resolve eq20729 eq21937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20729 eq21937
  have eq21987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21978
  have eq21993 : x = (M.op x y) := by
    first
    | (have r₁ := eq21987
       have r₂ := eq28
       grind)
    | exact resolve eq21987 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21987
  have eq22016 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21993 eq21
    | exact resolve eq21 eq21993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq22098 : y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq21993 eq1128
    | exact resolve eq1128 eq21993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq22105 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq22098
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22098
    | exact resolve eq22098 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22098
  have eq22159 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22016
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22016
    | exact resolve eq22016 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22016
  have eq22161 : y = (M.op x x) := by
    first
    | exact superpose eq21993 eq22105
    | exact resolve eq22105 eq21993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22105
  have eq22165 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq22159 eq27
    | exact resolve eq27 eq22159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22307 : (M.op x y) = (k y x) := by grind
  clear eq22161
  have eq22371 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq22307
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22307
    | exact resolve eq22307 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22307
  have eq22386 : x = (k y x) := by
    first
    | exact superpose eq21993 eq22371
    | exact resolve eq22371 eq21993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21993 eq22371
  have eq22467 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq22386
       grind)
    | exact superpose eq22386 eq73
    | exact resolve eq73 eq22386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq22482 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq842 x y
       have i₂ := eq22386
       grind)
    | exact superpose eq22386 eq842
    | (have j0 := eq842 x y
       grind)
    | exact resolve eq842 eq22386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842 eq22386
  have eq22485 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq22482
  have eq22493 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22485
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22485
    | exact resolve eq22485 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22485
  have eq22505 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq22159 eq22467
    | exact resolve eq22467 eq22159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22467
  have eq22507 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22493
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22493
    | exact resolve eq22493 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22493
  have eq22519 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22505
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22505
    | exact resolve eq22505 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22505
  have eq22521 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq22507
    | exact resolve eq22507 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22507
  have eq22532 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq22159 eq22519
    | exact resolve eq22519 eq22159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22519
  have eq22534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22159 eq22521
    | exact resolve eq22521 eq22159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22521
  have eq22541 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq22534
       have r₂ := eq28
       grind)
    | exact resolve eq22534 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22534
  have eq22548 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22541
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22541
    | exact resolve eq22541 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22541
  have eq22554 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22159 eq22548
    | exact resolve eq22548 eq22159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22159 eq22548
  have eq22560 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22554
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22554
    | exact resolve eq22554 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22554
  have eq22626 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq22560
  have eq22691 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq22165 eq22626
    | exact resolve eq22626 eq22165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22165 eq22626
  have eq22692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22532 eq22691
    | exact resolve eq22691 eq22532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22532 eq22691
  have eq22693 : False := by grind
  exact eq22693

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pxy_pyx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq480 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  clear eq90
  have eq488 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq489 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq488 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq493 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq489 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq489 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq489 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq502 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq493
    | (have j0 := eq493 X0 X1
       grind)
    | exact resolve eq493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq503 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq502 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq509 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq503 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq503
    | exact resolve eq503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq503 x y
       grind)
    | exact superpose eq503 eq16
    | exact resolve eq16 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq626 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq509 X0 (τ X1)
       grind)
    | exact superpose eq509 eq18
    | exact resolve eq18 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq509
  have eq639 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq626
    | exact resolve eq626 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq645 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq639
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq657 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq521
       have i₂ := eq645 x y
       grind)
    | exact superpose eq645 eq521
    | exact resolve eq521 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq645
  have eq658 : False := by grind
  exact eq658

/-- `Equation1849`: `x = (x ◇ (y ◇ x)) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_pyx_pxy_Equation1849 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1849 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1849.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op y (M.op x y)) (M.op y X0)) := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X0 (M.op x X0)) X3
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X0)) X0 X2
       have i₂ := eq14 X0 X1 (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 X0))) ≠ X0 ∨ (k (M.op X0 (M.op X2 X0)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq44
    | exact resolve eq44 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq50
    | exact resolve eq50 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq73
    | exact resolve eq73 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq71
    | exact resolve eq71 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x x) = (M.op y x) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq90 : (M.op x x) = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq379 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 X0
       have i₂ := eq11 X0 (τ X1)
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq456 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X2 (M.op (M.op X0 X1) X0))) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X0) X2 (M.op (M.op X0 X1) x)
       have i₂ := eq53 X0 X1 x
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1 (M.op X0 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq572 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq556 (M.op X1 X0) X0
       have i₂ := eq556 X0 X1
       grind)
    | exact superpose eq556 eq556
    | exact resolve eq556 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : (M.op y (M.op x y)) = (M.op y y) := by
    first
    | (have i₁ := eq556 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq556
    | (have j0 := eq556 y x
       grind)
    | exact resolve eq556 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq556
    | (have j0 := eq556 (σ y) (σ x)
       grind)
    | exact resolve eq556 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 (M.op X2 X0)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq556 X0 X2
       grind)
    | exact superpose eq556 eq68
    | (have j0 := eq68 X0 X1 X2
       grind)
    | exact resolve eq68 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq635 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1 x
       have i₂ := eq556 X0 x
       grind)
    | exact superpose eq556 eq634
    | (have j0 := eq634 X0 X1 x
       grind)
    | exact resolve eq634 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq673 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X0) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq635 X0 (M.op X0 (M.op X1 X0))
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq635
    | (have j0 := eq635 X0 (M.op X0 (M.op X1 X0))
       grind)
    | (have r₁ := eq635 x (M.op x (M.op X1 x))
       have r₂ := eq14 x X1 x
       grind)
    | exact resolve eq635 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : y ≠ y ∨ y = (k (M.op y y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq51 eq635
    | (have j0 := eq635 y (M.op y (M.op x y))
       grind)
    | (have r₁ := eq635 y (M.op y (M.op x y))
       have r₂ := eq51 y
       grind)
    | exact resolve eq635 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq677 : (σ y) ≠ (σ y) ∨ (σ y) = (k (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq52 eq635
    | (have j0 := eq635 (σ y) (M.op (σ y) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq635 (σ y) (M.op (σ y) (M.op (σ x) (σ y)))
       have r₂ := eq52 (σ y)
       grind)
    | exact resolve eq635 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq635
  have eq680 : (σ y) = (k (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by grind
  clear eq677
  have eq682 : y = (k (M.op y y) (M.op y (M.op x y))) := by grind
  clear eq675
  have eq684 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq687 : (σ y) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq583 eq680
    | exact resolve eq680 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq680
  have eq689 : y = (k (M.op y y) (M.op y y)) := by
    first
    | exact superpose eq582 eq682
    | exact resolve eq682 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq682
  have eq690 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq684 X0 x
       have i₂ := eq556 X0 x
       grind)
    | exact superpose eq556 eq684
    | exact resolve eq684 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq696 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq687
       have i₂ := eq69 (M.op sF3 sF3)
       grind)
    | exact superpose eq69 eq687
    | exact resolve eq687 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq698 : y = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq689
       have i₂ := eq69 (M.op y y)
       grind)
    | exact superpose eq69 eq689
    | exact resolve eq689 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq699 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq690 X0
       have i₂ := eq69 (M.op X0 X0)
       grind)
    | exact superpose eq69 eq690
    | exact resolve eq690 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq690
  have eq733 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq696 eq556
    | exact resolve eq556 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq756 : y = (M.op (M.op y y) y) := by
    first
    | (have i₁ := eq556 (M.op y y) (M.op y y)
       have i₂ := eq698
       grind)
    | exact superpose eq698 eq556
    | exact resolve eq556 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq945 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq80
    | (have j0 := eq80 X0 X1
       grind)
    | exact resolve eq80 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq80
  have eq1075 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq945 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq945
    | (have j0 := eq945 X0 y
       grind)
    | exact resolve eq945 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq6605 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ y = X0 ∨ (M.op X0 X0) = (M.op y X0) := by
    intro X0
    first
    | exact superpose eq30 eq379
    | exact resolve eq379 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq6645 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ y = X0 ∨ (M.op X0 X0) = (M.op y X0) := by
    intro X0
    first
    | exact superpose eq41 eq6605
    | (have j0 := eq6605 X0
       grind)
    | exact resolve eq6605 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq6605
  have eq7545 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1075 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1075
    | (have j0 := eq1075 x
       grind)
    | exact resolve eq1075 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq7570 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7545
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq7545
    | exact resolve eq7545 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7545
  have eq7593 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq7570
    | exact resolve eq7570 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7570
  have eq7606 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7593
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq7593
    | exact resolve eq7593 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7593
  have eq8567 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1 x
       have i₂ := eq556 (M.op (M.op X0 X1) X0) x
       grind)
    | exact superpose eq556 eq456
    | exact resolve eq456 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq8568 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8567 X0 X1
       have i₂ := eq53 X0 X1 X0
       grind)
    | exact superpose eq53 eq8567
    | exact resolve eq8567 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq8567
  have eq25578 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq90
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq25596 : (k x y) = (M.op x x) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq25578
  have eq25667 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 X1
       have i₂ := eq8568 X1 X0
       grind)
    | exact superpose eq8568 eq572
    | exact resolve eq572 eq8568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq8568
  have eq25857 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq556 X0 (M.op X0 X1)
       have i₂ := eq25667 X1 X0
       grind)
    | (have i₁ := eq556 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq25667 X0 X1
       grind)
    | exact superpose eq25667 eq556
    | exact resolve eq556 eq25667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq29961 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7606 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq7606
       grind)
    | exact resolve eq13 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29979 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7606 eq25667
    | exact resolve eq25667 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7606
  have eq29985 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq29961
  have eq29988 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29979
       have i₂ := eq699 sF2
       grind)
    | exact superpose eq699 eq29979
    | exact resolve eq29979 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29979
  have eq72185 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq25596
       grind)
    | exact superpose eq25596 eq45
    | exact resolve eq45 eq25596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq25596
  have eq72226 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq72185
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq72185
    | exact resolve eq72185 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq72185
  have eq75732 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq29985
  have eq83260 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq72226
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq72226
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq72226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72226
  have eq83292 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq83260
    | exact resolve eq83260 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83260
  have eq83295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq83292
    | exact resolve eq83292 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83292
  have eq83296 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq83295
       have r₂ := eq28
       grind)
    | exact resolve eq83295 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83295
  have eq83324 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq83296 eq25857
    | exact resolve eq25857 eq83296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83332 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq83324
       have i₂ := eq699 sF2
       grind)
    | exact superpose eq699 eq83324
    | exact resolve eq83324 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83324
  have eq83384 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq83332 eq733
    | exact resolve eq733 eq83332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq83332
  have eq84316 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq83296 eq83384
    | exact resolve eq83384 eq83296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83296 eq83384
  have eq84366 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq84316
  have eq86118 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq84366 eq29988
    | exact resolve eq29988 eq84366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29988 eq84366
  have eq86152 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq86118
  have eq86173 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq86152
       have r₂ := eq75732
       grind)
    | exact resolve eq86152 eq75732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75732 eq86152
  have eq86320 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq86173 eq61
    | exact resolve eq61 eq86173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq86173
  have eq116775 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6645 x
       have i₂ := eq86320
       grind)
    | exact superpose eq86320 eq6645
    | (have j0 := eq6645 x
       grind)
    | exact resolve eq6645 eq86320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6645 eq86320
  have eq116967 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq116775
  have eq117083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq116967
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq116967
    | exact resolve eq116967 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116967
  have eq117105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117083
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq117083
    | exact resolve eq117083 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117083
  have eq117114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq117105
    | exact resolve eq117105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117105
  have eq117118 : (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq117114
       have r₂ := eq28
       grind)
    | exact resolve eq117114 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117114
  have eq117145 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x x) y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25667 x y
       have i₂ := eq117118
       grind)
    | exact superpose eq117118 eq25667
    | exact resolve eq25667 eq117118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25667
  have eq117147 : (M.op y y) = (M.op y (M.op (M.op x x) (M.op x x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25857 y x
       have i₂ := eq117118
       grind)
    | exact superpose eq117118 eq25857
    | exact resolve eq25857 eq117118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25857
  have eq117156 : (M.op y y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117147
       have i₂ := eq699 x
       grind)
    | exact superpose eq699 eq117147
    | exact resolve eq117147 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117147
  have eq117158 : x = (M.op (M.op x x) y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117145
       have i₂ := eq699 x
       grind)
    | exact superpose eq699 eq117145
    | exact resolve eq117145 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq117145
  have eq117255 : y = (M.op (M.op y x) y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq756
       have i₂ := eq117156
       grind)
    | exact superpose eq117156 eq756
    | exact resolve eq756 eq117156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq117156
  have eq118259 : y = (M.op (M.op x x) y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117255
       have i₂ := eq117118
       grind)
    | exact superpose eq117118 eq117255
    | exact resolve eq117255 eq117118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117118 eq117255
  have eq118309 : y = (M.op (M.op x x) y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq118259
  have eq119583 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117158
       have i₂ := eq118309
       grind)
    | exact superpose eq118309 eq117158
    | exact resolve eq117158 eq118309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117158 eq118309
  have eq119619 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq119583
  have eq119649 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq119619 eq30
    | exact resolve eq30 eq119619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq119619
  have eq119842 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq119649
    | exact resolve eq119649 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq119649
  have eq119843 : x = y := by grind
  clear eq119842
  have eq119876 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq119843
       grind)
    | exact superpose eq119843 eq19
    | exact resolve eq19 eq119843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq119877 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq119843
       grind)
    | exact superpose eq119843 eq25
    | exact resolve eq25 eq119843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq119843
  have eq120204 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq119877
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq119877
    | exact resolve eq119877 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq119877
  have eq120252 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq120204 eq27
    | exact resolve eq27 eq120204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq120204
  have eq120713 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq120252 eq74
    | exact resolve eq74 eq120252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq120252
  have eq120850 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq120713
       have i₂ := eq119876
       grind)
    | exact superpose eq119876 eq120713
    | exact resolve eq120713 eq119876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119876 eq120713
  have eq120885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120850 eq15
    | exact resolve eq15 eq120850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120850
  have eq121227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq120885
    | exact resolve eq120885 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq120885
  have eq121332 : False := by grind
  exact eq121332

/-- `Equation2066`: `x = ((x ◇ y) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pyx_pxy_pyx_Equation2066 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2066 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2066.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq620 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq659 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq621 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq664 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq659 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq659 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq659 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq659 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq665 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq620 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq620 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq620 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq672 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq664 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq664
    | (have j0 := eq664 X0 X1
       grind)
    | exact resolve eq664 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq673 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq672 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq674 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq665
    | (have j0 := eq665 X0 X1
       grind)
    | exact resolve eq665 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq675 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq674 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq678 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq675 X0 X1
       have j1 := eq673 X0 X1
       grind)
    | (have r₁ := eq675 X0 X1
       have r₂ := eq673 X0 X1
       grind)
    | exact resolve eq675 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq675
  have eq679 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq678 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq678
    | exact resolve eq678 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq678 x y
       grind)
    | exact superpose eq678 eq16
    | exact resolve eq16 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq807 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq679 X0 (τ X1)
       grind)
    | exact superpose eq679 eq17
    | exact resolve eq17 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq679
  have eq839 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq807 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq807
    | exact resolve eq807 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq854 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq839 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq839
    | exact resolve eq839 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq891 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq690
       have i₂ := eq854 x y
       grind)
    | exact superpose eq854 eq690
    | exact resolve eq690 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq854
  have eq892 : False := by grind
  exact eq892

/-- `Equation2093`: `x = ((y ◇ x) ◇ x) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pyy_pyx_Equation2093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op X2 X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) y) (M.op X0 y)) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X0 (M.op X2 X0)) (M.op X3 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X0) (M.op (M.op x X0) X0) X3
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq66 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq79 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq83 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq83
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq113 : ∀ X0 : G, (σ (k (k y (M.op x y)) X0)) = (k (k (σ y) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq76 eq10
    | exact resolve eq10 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq116 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq153 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq136
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq136
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq153
  have eq207 : (σ (k (k (M.op x y) (M.op x y)) (M.op x y))) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq41
    | exact resolve eq41 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq213 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq222 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq228 : (σ y) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq222 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X1 : G, (M.op x y) = (M.op (M.op y (M.op x y)) (M.op X1 (M.op x y))) := by
    intro X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq254 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq34
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 (M.op (M.op x X0) X0)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (M.op (σ X0) (σ (k X0 X1))) (M.op X2 (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (σ X0) (σ X1) x
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq52
    | (have j1 := eq77 X0 X1
       grind)
    | exact resolve eq52 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq670 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq660 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq672 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq670 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq670 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq670 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq670 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq682 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq672
    | (have j0 := eq672 X0 X1
       grind)
    | exact resolve eq672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq3063 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq669 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq669
    | (have j0 := eq669 (τ X0)
       grind)
    | exact resolve eq669 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq669
  have eq3071 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3063 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3063
    | (have j0 := eq3063 X0
       grind)
    | exact resolve eq3063 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063
  have eq3077 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3071 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3071
    | (have j0 := eq3071 X0
       grind)
    | exact resolve eq3071 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3071
  have eq3172 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78
    | (have j0 := eq78 x
       grind)
    | exact resolve eq78 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3186 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3172
  have eq3191 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3186
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3186
    | exact resolve eq3186 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3186
  have eq3209 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3191
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3191 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191
  have eq3214 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3209 eq49
    | exact resolve eq49 eq3209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3329 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq79 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq79
    | (have j0 := eq79 y
       grind)
    | exact resolve eq79 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3344 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3329
  have eq3348 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3344
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq3344
    | exact resolve eq3344 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq3373 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3348
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3348 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq3394 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3373 eq107
    | exact resolve eq107 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq3655 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq137
    | (have j0 := eq137 (M.op x y)
       grind)
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq3667 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3655
  have eq3670 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq3667
    | exact resolve eq3667 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667
  have eq3702 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3670
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3670 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670
  have eq3739 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3702 eq159
    | exact resolve eq159 eq3702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq5221 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq254
    | exact resolve eq254 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq5311 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5221 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq5221
    | (have j0 := eq5221 X0 X1
       grind)
    | exact resolve eq5221 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5221
  have eq9105 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ (k (k X0 X1) X0)) (M.op X2 (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq664 X0 X1 X2
       have i₂ := eq77 (k X0 X1) X0
       grind)
    | exact superpose eq77 eq664
    | (have j0 := eq664 X0 X1 X2
       have j1 := eq77 X0 X1
       grind)
    | exact resolve eq664 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq664
  have eq15002 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3209 eq90
    | exact resolve eq90 eq3209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq15290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15290
    | exact resolve eq15290 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15290
  have eq15311 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq15300
       have r₂ := eq27
       grind)
    | exact resolve eq15300 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15300
  have eq15313 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15311
    | exact resolve eq15311 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15311
  have eq15315 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15313 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15313
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15313
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15313
       grind)
    | exact resolve eq12 eq15313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15317 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ x)) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq15313 eq14
    | exact resolve eq14 eq15313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15329 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq15315
  have eq15335 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15329
    | exact resolve eq15329 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15329
  have eq15336 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq15335
  have eq15510 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3373 eq108
    | exact resolve eq108 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq15827 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15336 eq101
    | exact resolve eq101 eq15336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15336
  have eq15844 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15827
  have eq16483 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq15313 eq15317
    | exact resolve eq15317 eq15313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16489 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15313 eq15317
    | exact resolve eq15317 eq15313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15313 eq15317
  have eq16509 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq16489
  have eq16512 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq16483 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16483
  have eq16650 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16509 eq3394
    | exact resolve eq3394 eq16509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16509
  have eq16689 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq28 eq16650
    | exact resolve eq16650 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16650
  have eq16700 : ∀ X0 : G, x = (M.op (M.op y x) (M.op X0 x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq16689
       grind)
    | exact superpose eq16689 eq14
    | exact resolve eq14 eq16689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16933 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15844 eq16512
    | exact resolve eq16512 eq15844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15844 eq16512
  have eq16955 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq16933
  have eq16970 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3702 eq160
    | exact resolve eq160 eq3702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq19027 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16700 y
       have i₂ := eq16689
       grind)
    | exact superpose eq16689 eq16700
    | exact resolve eq16700 eq16689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16689 eq16700
  have eq19049 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19027
  have eq19230 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq19049
       grind)
    | exact superpose eq19049 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq19049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19247 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19230
  have eq19316 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq19247
       grind)
    | exact superpose eq19247 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq19247
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19247
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19247
       grind)
    | exact resolve eq13 eq19247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19328 : x ≠ y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19247
  have eq19329 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19316
  have eq19574 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19049
       have i₂ := eq19329
       grind)
    | exact superpose eq19329 eq19049
    | exact resolve eq19049 eq19329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19049 eq19329
  have eq19602 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19574
  have eq19619 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19602
       have r₂ := eq19328
       grind)
    | exact resolve eq19602 eq19328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19328 eq19602
  have eq19646 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq19619
       grind)
    | exact superpose eq19619 eq53
    | exact resolve eq53 eq19619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq19649 : x ≠ y ∨ x = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq19619
       grind)
    | exact superpose eq19619 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq19619
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19619
       grind)
    | exact resolve eq13 eq19619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19652 : ∀ X0 : G, x = (M.op (M.op y x) (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq52 y y x
       have i₂ := eq19619
       grind)
    | exact superpose eq19619 eq52
    | exact resolve eq52 eq19619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19656 : x = (M.op (M.op y x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq419 y y
       have i₂ := eq19619
       grind)
    | exact superpose eq19619 eq419
    | exact resolve eq419 eq19619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19666 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19646
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19646
    | exact resolve eq19646 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19646
  have eq19679 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19666 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq19666
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19666
       grind)
    | exact resolve eq13 eq19666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22278 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15510
       have i₂ := eq19619
       grind)
    | exact superpose eq19619 eq15510
    | exact resolve eq15510 eq19619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19619
  have eq22339 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22278
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22278
    | exact resolve eq22278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22278
  have eq22341 : (τ (σ x)) = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22339 eq3394
    | exact resolve eq3394 eq22339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3394 eq22339
  have eq22387 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq22341
    | exact resolve eq22341 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22341
  have eq22392 : x = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22387
       have r₂ := eq19649
       grind)
    | exact resolve eq22387 eq19649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19649 eq22387
  have eq22398 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq22392
       grind)
    | exact superpose eq22392 eq75
    | exact resolve eq75 eq22392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq22392
  have eq22445 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3373 eq22398
    | exact resolve eq22398 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373 eq22398
  have eq22462 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22445
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22445
    | exact resolve eq22445 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22445
  have eq22510 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ x)) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22462 eq52
    | exact resolve eq52 eq22462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22514 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22462 eq419
    | exact resolve eq419 eq22462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22462
  have eq22987 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19666 eq16970
    | exact resolve eq16970 eq19666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19666
  have eq23051 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22987
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22987
    | exact resolve eq22987 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22987
  have eq23251 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23051 eq3739
    | exact resolve eq3739 eq23051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23051
  have eq23286 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq23251
    | exact resolve eq23251 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23251
  have eq23287 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23286
       have r₂ := eq19679
       grind)
    | exact resolve eq23286 eq19679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19679 eq23286
  have eq23289 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23287 eq136
    | exact resolve eq136 eq23287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23333 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3702 eq23289
    | exact resolve eq23289 eq3702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23289
  have eq23350 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23333
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23333
    | exact resolve eq23333 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23333
  have eq23386 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23350 eq14
    | exact resolve eq14 eq23350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23388 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23350 eq52
    | exact resolve eq52 eq23350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25403 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23350 eq23386
    | exact resolve eq23386 eq23350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23350 eq23386
  have eq25425 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25403
  have eq25431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16955 eq25425
    | exact resolve eq25425 eq16955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16955 eq25425
  have eq25457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq25431
  have eq25458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq25457
    | exact resolve eq25457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25457
  have eq25459 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25458
       have r₂ := eq27
       grind)
    | exact resolve eq25458 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25458
  have eq25481 : ∀ X0 : G, x = (M.op y (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19652 X0
       have i₂ := eq25459
       grind)
    | exact superpose eq25459 eq19652
    | exact resolve eq19652 eq25459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19652
  have eq25488 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq25459
       grind)
    | exact superpose eq25459 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25459
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25459
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25459
       grind)
    | exact resolve eq13 eq25459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25459
  have eq25500 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25488
  have eq25507 : ∀ X0 : G, x = (M.op y (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq25481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25481
  have eq25514 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25500
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25500
    | exact resolve eq25500 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25500
  have eq25522 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq25514
       grind)
    | exact superpose eq25514 eq44
    | exact resolve eq44 eq25514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25514
  have eq25561 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq25522
    | exact resolve eq25522 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25522
  have eq25656 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25561 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq25561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25676 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq25656
    | exact resolve eq25656 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25656
  have eq25677 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25676
  have eq30636 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25677 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq25677
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25677
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25677
       grind)
    | exact resolve eq13 eq25677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25677
  have eq30649 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30636
  have eq30667 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq30649
    | exact resolve eq30649 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30649
  have eq31007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30667 eq25561
    | exact resolve eq25561 eq30667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25561 eq30667
  have eq31022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq31007
  have eq31031 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31022
       have r₂ := eq27
       grind)
    | exact resolve eq31022 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31022
  have eq31040 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31031 eq22514
    | exact resolve eq22514 eq31031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22514
  have eq31046 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31031 eq22510
    | exact resolve eq22510 eq31031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22510 eq31031
  have eq31062 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31046
  have eq31068 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31040
  have eq31404 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31062 eq3739
    | exact resolve eq3739 eq31062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31062
  have eq31463 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq31404
    | exact resolve eq31404 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31404
  have eq31498 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31068 eq23388
    | exact resolve eq23388 eq31068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23388 eq31068
  have eq31514 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31498
  have eq31549 : x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31463 eq23287
    | exact resolve eq23287 eq31463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23287 eq31463
  have eq31582 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq31549
  have eq31666 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31514 eq3214
    | exact resolve eq3214 eq31514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31514
  have eq31730 : y = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq31666
    | exact resolve eq31666 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31666
  have eq31838 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3077 x
       have i₂ := eq31730
       grind)
    | exact superpose eq31730 eq3077
    | (have j0 := eq3077 x
       grind)
    | exact resolve eq3077 eq31730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31730
  have eq31877 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31838
       have r₂ := eq31582
       grind)
    | exact resolve eq31838 eq31582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31582 eq31838
  have eq32044 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25507 x
       have i₂ := eq31877
       grind)
    | exact superpose eq31877 eq25507
    | exact resolve eq25507 eq31877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25507 eq31877
  have eq32068 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32044
  have eq32435 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19656
       have i₂ := eq32068
       grind)
    | exact superpose eq32068 eq19656
    | exact resolve eq19656 eq32068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19656 eq32068
  have eq32465 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32435
  have eq32478 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32465
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32465
    | exact resolve eq32465 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32465
  have eq32479 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32478
  have eq32483 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32479 eq27
    | exact resolve eq27 eq32479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32486 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32479 eq66
    | (have r₁ := eq66
       have r₂ := eq32479
       grind)
    | exact resolve eq66 eq32479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq32487 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32479 eq116
    | (have r₁ := eq116
       have r₂ := eq32479
       grind)
    | exact resolve eq116 eq32479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq32488 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32479 eq222
    | exact resolve eq222 eq32479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq32492 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ x)) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32479 eq240
    | exact resolve eq240 eq32479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq32500 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32487
  have eq32501 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32486
  have eq32504 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq32488
    | exact resolve eq32488 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32488
  have eq32509 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32479 eq32504
    | exact resolve eq32504 eq32479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32541 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32509
  have eq32565 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32541 eq3214
    | exact resolve eq3214 eq32541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32632 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq32565
    | exact resolve eq32565 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32565
  have eq32656 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3077 x
       have i₂ := eq32632
       grind)
    | exact superpose eq32632 eq3077
    | (have j0 := eq3077 x
       grind)
    | exact resolve eq3077 eq32632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3077
  have eq32658 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq32632
       grind)
    | exact superpose eq32632 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq32632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32675 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq32658
  have eq32828 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32501 eq101
    | exact resolve eq101 eq32501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq32501
  have eq32849 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq32828
  have eq33103 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32479 eq228
    | exact resolve eq228 eq32479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq32479
  have eq33108 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq33103
    | exact resolve eq33103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33103
  have eq33111 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq33108
    | exact resolve eq33108 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33108
  have eq36452 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32849 eq32492
    | exact resolve eq32492 eq32849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32492
  have eq36466 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq36452
  have eq37093 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq36466 eq3739
    | exact resolve eq3739 eq36466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36466
  have eq37149 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq28 eq37093
    | exact resolve eq37093 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq37093
  have eq37621 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq52 x x x
       have i₂ := eq32675
       grind)
    | exact superpose eq32675 eq52
    | exact resolve eq52 eq32675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32675
  have eq37643 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq37621 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37621
    | (have j0 := eq37621 X0
       grind)
    | exact resolve eq37621 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37621
  have eq37963 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq37149
       grind)
    | exact superpose eq37149 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq37149
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq37149
       grind)
    | exact resolve eq13 eq37149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37964 : ∀ X0 : G, x = (M.op (M.op y x) (M.op X0 x)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq37149
       grind)
    | exact superpose eq37149 eq14
    | exact resolve eq14 eq37149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37975 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq37963
  have eq37992 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq37975
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37975
    | exact resolve eq37975 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37975
  have eq38370 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq37992
       grind)
    | exact superpose eq37992 eq44
    | exact resolve eq44 eq37992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37992
  have eq38409 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq38370
    | exact resolve eq38370 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38370
  have eq63772 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32500 eq38409
    | exact resolve eq38409 eq32500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32500
  have eq63788 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq63772
  have eq65378 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq234 eq37643
    | (have j0 := eq37643 x
       grind)
    | exact resolve eq37643 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq37643
  have eq65412 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65378 eq16970
    | exact resolve eq16970 eq65378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16970
  have eq65416 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65378 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq65378
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq65378
       grind)
    | exact resolve eq13 eq65378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65378
  have eq65428 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65412
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65412
    | exact resolve eq65412 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65412
  have eq92707 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65428 eq3739
    | exact resolve eq3739 eq65428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3739 eq65428
  have eq92756 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq92707
    | exact resolve eq92707 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92707
  have eq92757 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq92756
       have r₂ := eq65416
       grind)
    | exact resolve eq92756 eq65416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65416 eq92756
  have eq145162 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq37964 y
       have i₂ := eq37149
       grind)
    | exact superpose eq37149 eq37964
    | exact resolve eq37964 eq37149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37149 eq37964
  have eq145196 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq145162
  have eq146044 : x = y ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq145196 eq92757
    | exact resolve eq92757 eq145196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145196
  have eq146065 : x = y ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq146044
  have eq146087 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq146065
       have r₂ := eq32656
       grind)
    | exact resolve eq146065 eq32656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146065
  have eq146214 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15510
       have i₂ := eq146087
       grind)
    | exact superpose eq146087 eq15510
    | exact resolve eq15510 eq146087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15510 eq146087
  have eq146252 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq146214
       have r₂ := eq32656
       grind)
    | exact resolve eq146214 eq32656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146214
  have eq146257 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq146252
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq146252
    | exact resolve eq146252 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146252
  have eq468237 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq63788 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq63788
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq63788
       grind)
    | exact resolve eq13 eq63788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63788
  have eq468253 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq468237
  have eq468353 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq468253
    | exact resolve eq468253 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468253
  have eq595148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq468353 eq38409
    | exact resolve eq38409 eq468353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38409 eq468353
  have eq595187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq595148
  have eq595208 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq595187
       have r₂ := eq27
       grind)
    | exact resolve eq595187 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595187
  have eq595241 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq595208 eq146257
    | exact resolve eq146257 eq595208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146257 eq595208
  have eq595330 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq595241
  have eq595355 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq595330
       have r₂ := eq32483
       grind)
    | exact resolve eq595330 eq32483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32483 eq595330
  have eq595765 : x = y ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq595355 eq92757
    | exact resolve eq92757 eq595355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92757 eq595355
  have eq595846 : x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq595765
  have eq595909 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq595846
       have r₂ := eq32656
       grind)
    | exact resolve eq595846 eq32656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32656 eq595846
  have eq596079 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq595909
       grind)
    | exact superpose eq595909 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq595909
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq595909
       grind)
    | exact resolve eq13 eq595909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595909
  have eq596095 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq596079
  have eq596150 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32632
       have i₂ := eq596095
       grind)
    | exact superpose eq596095 eq32632
    | exact resolve eq32632 eq596095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32632
  have eq596406 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq682 x x
       have i₂ := eq596095
       grind)
    | exact superpose eq596095 eq682
    | (have j0 := eq682 x x
       grind)
    | exact resolve eq682 eq596095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq596095
  have eq596428 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq596406
  have eq596429 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq596428
  have eq596660 : x = (M.op x y) ∨ x = y := by grind
  clear eq596150
  have eq596690 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq596429
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq596429
    | exact resolve eq596429 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596429
  have eq596912 : y = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq596660 eq213
    | exact resolve eq213 eq596660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597184 : y = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq596912
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq596912
    | exact resolve eq596912 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596912
  have eq598110 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq596690 eq32541
    | exact resolve eq32541 eq596690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596690
  have eq598592 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq598110
  have eq598638 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq598592 eq26
    | exact resolve eq26 eq598592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598592
  have eq599805 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq596660 eq597184
    | exact resolve eq597184 eq596660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596660 eq597184
  have eq599840 : y = (M.op x x) ∨ x = y := by grind
  clear eq599805
  have eq599993 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq598638 eq32541
    | exact resolve eq32541 eq598638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32541 eq598638
  have eq600488 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq599993
  have eq600514 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq600488 eq27
    | exact resolve eq27 eq600488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600564 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq600488 eq32504
    | exact resolve eq32504 eq600488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32504
  have eq600572 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq600488 eq33111
    | (have r₁ := eq33111
       have r₂ := eq600488
       grind)
    | exact resolve eq33111 eq600488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33111 eq600488
  have eq600591 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq600572
  have eq600592 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq600591
  have eq600603 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq600564
  have eq600645 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq600592
    | exact resolve eq600592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600592
  have eq600654 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq15002
       have i₂ := eq599840
       grind)
    | exact superpose eq599840 eq15002
    | exact resolve eq15002 eq599840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15002 eq599840
  have eq600723 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq600654
  have eq600739 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq600723
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq600723
    | exact resolve eq600723 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600723
  have eq600767 : (τ (σ y)) = (k x x) ∨ x = y := by
    first
    | exact superpose eq600739 eq3214
    | exact resolve eq3214 eq600739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3214 eq600739
  have eq600940 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq29 eq600767
    | exact resolve eq600767 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600767
  have eq601127 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq600603 eq32849
    | exact resolve eq32849 eq600603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32849 eq600603
  have eq601297 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq601127
  have eq601361 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq601297
       have r₂ := eq600514
       grind)
    | exact resolve eq601297 eq600514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600514 eq601297
  have eq602970 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq601361
       grind)
    | exact superpose eq601361 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq601361
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq601361
       grind)
    | exact resolve eq13 eq601361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601361
  have eq602986 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq602970
  have eq603014 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq602986
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq602986
    | exact resolve eq602986 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602986
  have eq624531 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq603014
       grind)
    | exact superpose eq603014 eq44
    | exact resolve eq44 eq603014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603014
  have eq624672 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq624531
    | exact resolve eq624531 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624531
  have eq638943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq624672 eq600645
    | exact resolve eq600645 eq624672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600645 eq624672
  have eq638979 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq638943
  have eq639001 : x = (M.op x y) := by
    first
    | (have r₁ := eq638979
       have r₂ := eq27
       grind)
    | exact resolve eq638979 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638979
  have eq645718 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq639001 eq20
    | exact resolve eq20 eq639001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645723 : x ≠ x ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq639001 eq65
    | (have r₁ := eq65
       have r₂ := eq639001
       grind)
    | exact resolve eq65 eq639001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq645771 : y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq639001 eq213
    | exact resolve eq213 eq639001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq645777 : ∀ X0 : G, x = (M.op (M.op y x) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq639001 eq235
    | exact resolve eq235 eq639001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq645942 : (k y x) = (M.op y x) := by grind
  clear eq645723
  have eq646047 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq645771
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq645771
    | exact resolve eq645771 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645771
  have eq646095 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq645718
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq645718
    | exact resolve eq645718 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645718
  have eq646100 : y = (M.op x x) := by
    first
    | exact superpose eq639001 eq646047
    | exact resolve eq646047 eq639001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646047
  have eq646153 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq646095 eq26
    | exact resolve eq26 eq646095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq648302 : x ≠ y ∨ y = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq646100
       grind)
    | exact superpose eq646100 eq13
    | exact resolve eq13 eq646100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648339 : y = (k x x) := by
    first
    | (have r₁ := eq648302
       have r₂ := eq600940
       grind)
    | exact resolve eq648302 eq600940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600940 eq648302
  have eq648476 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq648339
       grind)
    | exact superpose eq648339 eq43
    | exact resolve eq43 eq648339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq648339
  have eq648719 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3209 eq648476
    | exact resolve eq648476 eq3209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3209 eq648476
  have eq648791 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq646095 eq648719
    | exact resolve eq648719 eq646095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648719
  have eq648857 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq648791
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq648791
    | exact resolve eq648791 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648791
  have eq650609 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq648857 eq14
    | exact resolve eq14 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650610 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq648857 eq14
    | exact resolve eq14 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650611 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq648857 eq52
    | exact resolve eq52 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq650615 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq648857 eq419
    | exact resolve eq419 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq650641 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq646153 eq650615
    | exact resolve eq650615 eq646153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650615
  have eq650642 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq646153 eq650611
    | exact resolve eq650611 eq646153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650611
  have eq652635 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq645942
       grind)
    | exact superpose eq645942 eq74
    | exact resolve eq74 eq645942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq652812 : (k (σ y) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq646095 eq652635
    | exact resolve eq652635 eq646095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652635
  have eq655562 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq239 eq650642
    | (have j0 := eq650642 (σ x)
       grind)
    | exact resolve eq650642 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq650642
  have eq655948 : (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ (M.op x y)))) = (σ (k (k y (M.op x y)) (M.op y x))) := by
    first
    | (have i₁ := eq113 (M.op y x)
       have i₂ := eq652812
       grind)
    | exact superpose eq652812 eq113
    | exact resolve eq113 eq652812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq656270 : (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ (M.op x y)))) = (σ (k (k y x) (M.op y x))) := by
    first
    | exact superpose eq639001 eq655948
    | exact resolve eq655948 eq639001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655948
  have eq656333 : (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ (M.op x y)))) = (σ (k (M.op y x) (M.op y x))) := by
    first
    | (have i₁ := eq656270
       have i₂ := eq645942
       grind)
    | exact superpose eq645942 eq656270
    | exact resolve eq656270 eq645942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656270
  have eq666177 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq648857 eq650609
    | exact resolve eq650609 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650609
  have eq942712 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (k (k (M.op x y) (M.op x y)) (M.op x y))) (M.op X0 (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq136 eq9105
    | (have j0 := eq9105 (M.op x y) (M.op x y) x
       grind)
    | exact resolve eq9105 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq9105
  have eq942835 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (k (k (M.op x y) (M.op x y)) (M.op x y))) (M.op X0 (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq942712 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942712
  have eq942941 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (k (k (M.op x y) (M.op x y)) (M.op x y))) (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3702 eq942835
    | exact resolve eq942835 eq3702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942835
  have eq943473 : ∀ X0 : G, (σ y) = (M.op (σ (k (k (M.op x y) (M.op x y)) (M.op x y))) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq648857 eq942941
    | exact resolve eq942941 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942941
  have eq943966 : ∀ X0 : G, (σ y) = (M.op (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq207 eq943473
    | exact resolve eq943473 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq943473
  have eq944440 : ∀ X0 : G, (σ y) = (M.op (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3702 eq943966
    | exact resolve eq943966 eq3702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943966
  have eq944895 : ∀ X0 : G, (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq648857 eq944440
    | exact resolve eq944440 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944440
  have eq945316 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq944895
    | (have j0 := eq944895 X0
       grind)
    | exact resolve eq944895 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944895
  have eq945716 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq648857 eq945316
    | (have j0 := eq945316 X0
       grind)
    | exact resolve eq945316 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945316
  have eq946083 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq945716
    | (have j0 := eq945716 X0
       grind)
    | exact resolve eq945716 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945716
  have eq946384 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3702 eq946083
    | (have j0 := eq946083 X0
       grind)
    | exact resolve eq946083 eq3702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946083
  have eq946662 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq648857 eq946384
    | (have j0 := eq946384 X0
       grind)
    | exact resolve eq946384 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946384
  have eq946921 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq3702 eq946662
    | (have j0 := eq946662 X0
       grind)
    | exact resolve eq946662 eq3702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3702 eq946662
  have eq947170 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq648857 eq946921
    | (have j0 := eq946921 X0
       grind)
    | exact resolve eq946921 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946921
  have eq947356 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq20 eq947170
    | (have j0 := eq947170 X0
       grind)
    | exact resolve eq947170 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq947170
  have eq947505 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq646153 eq947356
    | (have j0 := eq947356 X0
       grind)
    | exact resolve eq947356 eq646153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947356
  have eq947631 : ∀ X0 : G, (σ y) = (M.op (k (σ y) (σ (M.op x y))) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq947505 X0
       grind)
    | (have r₁ := eq947505 X0
       have r₂ := eq27
       grind)
    | exact resolve eq947505 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947505
  have eq1624061 : (σ y) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq650610 eq947631
    | exact resolve eq947631 eq650610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650610 eq947631
  have eq1624293 : (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ (M.op x y)))) = (σ (M.op (M.op y x) (M.op y x))) ∨ (M.op y x) = (M.op (M.op y x) (M.op y x)) ∨ (M.op y x) = (M.op (M.op y x) (M.op y x)) := by
    first
    | (have i₁ := eq5311 (M.op y x) (M.op y x)
       have i₂ := eq656333
       grind)
    | exact superpose eq656333 eq5311
    | (have j0 := eq5311 (M.op y x) (M.op y x)
       grind)
    | exact resolve eq5311 eq656333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5311 eq656333
  have eq1624828 : (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ (M.op x y)))) = (σ (M.op (M.op y x) (M.op y x))) ∨ (M.op y x) = (M.op (M.op y x) (M.op y x)) := by grind
  clear eq1624293
  have eq1624988 : (σ x) = (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ (M.op x y)))) ∨ (M.op y x) = (M.op (M.op y x) (M.op y x)) := by
    first
    | (have i₁ := eq1624828
       have i₂ := eq645777 y
       grind)
    | exact superpose eq645777 eq1624828
    | exact resolve eq1624828 eq645777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624828
  have eq1625093 : (σ x) = (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ (M.op x y)))) ∨ (M.op y x) = (M.op (M.op y x) (M.op y x)) := by
    first
    | (have i₁ := eq1624988
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1624988
    | exact resolve eq1624988 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624988
  have eq1625168 : (σ (M.op x y)) = (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ (M.op x y)))) ∨ (M.op y x) = (M.op (M.op y x) (M.op y x)) := by
    first
    | exact superpose eq646095 eq1625093
    | exact resolve eq1625093 eq646095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625093
  have eq1625203 : (σ (M.op x y)) = (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ (M.op x y)))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1625168
       have i₂ := eq645777 y
       grind)
    | exact superpose eq645777 eq1625168
    | exact resolve eq1625168 eq645777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625168
  have eq1625260 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) (σ y))) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1625203
       have i₂ := eq11 sF3 sF1
       grind)
    | exact superpose eq11 eq1625203
    | (have j1 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq1625203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625203
  have eq1625374 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq646153 eq1625260
    | exact resolve eq1625260 eq646153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625260
  have eq1625377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq646153 eq1625374
    | exact resolve eq1625374 eq646153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625374
  have eq1625378 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1625377
       have r₂ := eq27
       grind)
    | exact resolve eq1625377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625377
  have eq1625411 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1625378 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq1625378
       grind)
    | exact resolve eq12 eq1625378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625378
  have eq1625429 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq1625411
  have eq1625440 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq646153 eq1625429
    | exact resolve eq1625429 eq646153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625429
  have eq1625451 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1625440
       have r₂ := eq27
       grind)
    | exact resolve eq1625440 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625440
  have eq1625456 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq648857 eq1625451
    | exact resolve eq1625451 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625451
  have eq1625709 : (τ (σ y)) = (k y (M.op x y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1625456 eq114
    | exact resolve eq114 eq1625456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1625456
  have eq1625834 : (τ (σ y)) = (k y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq639001 eq1625709
    | exact resolve eq1625709 eq639001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625709
  have eq1625849 : (τ (σ y)) = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1625834
       have i₂ := eq645942
       grind)
    | exact superpose eq645942 eq1625834
    | exact resolve eq1625834 eq645942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645942 eq1625834
  have eq1625858 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq1625849
    | exact resolve eq1625849 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625849
  have eq1625872 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1625858 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq1625858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625858
  have eq1625971 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq1625872
  have eq1625978 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq655562 eq1625971
    | exact resolve eq1625971 eq655562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625971
  have eq1625983 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq655562 eq1625978
    | exact resolve eq1625978 eq655562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625978
  have eq1671584 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq652812
       have i₂ := eq1625983
       grind)
    | exact superpose eq1625983 eq652812
    | exact resolve eq652812 eq1625983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652812
  have eq1671624 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1625983
       grind)
    | exact superpose eq1625983 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1625983
       grind)
    | exact resolve eq13 eq1625983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625983
  have eq1671641 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1671624
  have eq1671651 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1671641
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1671641
    | exact resolve eq1671641 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1671641
  have eq1671674 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1671584
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1671584
    | exact resolve eq1671584 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671584
  have eq1671688 : x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq639001 eq1671651
    | exact resolve eq1671651 eq639001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671651
  have eq1672870 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1671674 eq1624061
    | exact resolve eq1624061 eq1671674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624061 eq1671674
  have eq1672965 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1672870
  have eq1673108 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1671688
       grind)
    | exact superpose eq1671688 eq44
    | exact resolve eq44 eq1671688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1671688
  have eq1673393 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq646095 eq1673108
    | exact resolve eq1673108 eq646095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673108
  have eq1673506 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1673393
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1673393
    | exact resolve eq1673393 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673393
  have eq1673615 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq646095 eq1673506
    | exact resolve eq1673506 eq646095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673506
  have eq1674261 : (σ y) ≠ (σ y) ∨ (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1672965 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ y)
       have r₂ := eq1672965
       grind)
    | exact resolve eq13 eq1672965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672965
  have eq1674277 : (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1674261
  have eq1674291 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq646153 eq1674277
    | exact resolve eq1674277 eq646153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674277
  have eq1674515 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1674291 eq1673615
    | exact resolve eq1673615 eq1674291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673615 eq1674291
  have eq1674579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1674515
  have eq1674587 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1674579
       have r₂ := eq27
       grind)
    | exact resolve eq1674579 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674579
  have eq1674675 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq645777 y
       have i₂ := eq1674587
       grind)
    | exact superpose eq1674587 eq645777
    | exact resolve eq645777 eq1674587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645777 eq1674587
  have eq1674728 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1674675
       have i₂ := eq646100
       grind)
    | exact superpose eq646100 eq1674675
    | exact resolve eq1674675 eq646100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646100 eq1674675
  have eq1674958 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1674728 eq650641
    | exact resolve eq650641 eq1674728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650641
  have eq1674963 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1674728 eq655562
    | exact resolve eq655562 eq1674728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655562 eq1674728
  have eq1675424 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1674958 eq666177
    | exact resolve eq666177 eq1674958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666177 eq1674958
  have eq1677186 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1675424 eq1674963
    | exact resolve eq1674963 eq1675424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674963 eq1675424
  have eq1677258 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1677186
  have eq1677326 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1677258 eq29
    | exact resolve eq29 eq1677258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1677258
  have eq1678235 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1677326
    | exact resolve eq1677326 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1677326
  have eq1678393 : x = y ∨ x = y := by
    first
    | exact superpose eq639001 eq1678235
    | exact resolve eq1678235 eq639001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639001 eq1678235
  have eq1678394 : x = y := by grind
  clear eq1678393
  have eq1678779 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1678394
       grind)
    | exact superpose eq1678394 eq24
    | exact resolve eq24 eq1678394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1678394
  have eq1679597 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1678779
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1678779
    | exact resolve eq1678779 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1678779
  have eq1679819 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq646095 eq1679597
    | exact resolve eq1679597 eq646095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646095 eq1679597
  have eq1680788 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1679819 eq646153
    | exact resolve eq646153 eq1679819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646153
  have eq1680936 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq648857 eq1680788
    | exact resolve eq1680788 eq648857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648857 eq1680788
  have eq1681162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1679819 eq1680936
    | exact resolve eq1680936 eq1679819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679819 eq1680936
  have eq1681343 : False := by grind
  exact eq1681343

/-- `Equation2260`: `x = (x ◇ (y ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyx_pyx_pyy_pyx_Equation2260 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op (M.op X0 (M.op X1 (M.op X0 X2))) (M.op X3 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X0 X2))) X3 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3))) X2
       have i₂ := eq9 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq39
    | exact resolve eq39 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq39
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq142 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) (M.op (M.op X0 x) (M.op X1 x))
       have i₂ := eq20 X1 X0 x x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq201 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (M.op X1 X0) X2 X1
       have i₂ := eq9 X0 (M.op X1 X0) X2
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq245 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X1)) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 (M.op X1 X0) (M.op X0 X1) X2
       have i₂ := eq142 X1 X0
       grind)
    | exact superpose eq142 eq201
    | exact resolve eq201 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq274 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X1 X0) X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq245 X0 X1 X2
       have i₂ := eq142 X0 X1
       grind)
    | exact superpose eq142 eq245
    | exact resolve eq245 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq245
  have eq288 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq274 (σ X0) (σ X0) x
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq274
    | exact resolve eq274 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq404 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq364
    | (have j0 := eq364 X0 X1
       grind)
    | exact resolve eq364 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq364
  have eq412 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq404 X0 X1
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq404 X1 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq404 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq404
  have eq418 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq412 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq412
    | (have j0 := eq412 X0 X1
       grind)
    | exact resolve eq412 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq412
  have eq1232 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq418
    | exact resolve eq418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1244 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq418 (σ X1) X0
       grind)
    | exact superpose eq418 eq15
    | (have j1 := eq418 (σ X1) X0
       grind)
    | exact resolve eq15 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq1263 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1244 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq1244
    | (have j0 := eq1244 X0 X1
       grind)
    | exact resolve eq1244 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1281 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1232 (τ X0) X1
       grind)
    | exact superpose eq1232 eq18
    | (have j1 := eq1232 (τ X0) X1
       grind)
    | exact resolve eq18 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1232
  have eq7284 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1281 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1281
    | exact resolve eq1281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq7361 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7284 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7284
    | (have j0 := eq7284 X0 X1
       grind)
    | exact resolve eq7284 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7284
  have eq18319 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1263 x y
       grind)
    | exact superpose eq1263 eq16
    | (have j1 := eq1263 x y
       grind)
    | exact resolve eq16 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq18529 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18319
       have i₂ := eq7361 x y
       grind)
    | exact superpose eq7361 eq18319
    | (have j1 := eq7361 x y
       grind)
    | (have r₁ := eq18319
       have r₂ := eq7361 x y
       grind)
    | exact resolve eq18319 eq7361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7361 eq18319
  have eq18530 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq18529
  have eq18603 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) (M.op (σ (M.op y y)) X0))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq274 (σ y) (σ x) x
       have i₂ := eq18530
       grind)
    | exact superpose eq18530 eq274
    | exact resolve eq274 eq18530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18530
  have eq18627 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18603 x
       have i₂ := eq288 y x
       grind)
    | exact superpose eq288 eq18603
    | exact resolve eq18603 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq18603
  have eq18810 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18627
       grind)
    | exact superpose eq18627 eq10
    | exact resolve eq10 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18627
  have eq18879 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18810
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18810
    | exact resolve eq18810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18810
  have eq18884 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18879
       grind)
    | exact superpose eq18879 eq16
    | exact resolve eq16 eq18879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18879
  have eq18886 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq18884
       have r₂ := eq41 x
       grind)
    | exact resolve eq18884 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18884
  have eq19580 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq274 y y x
       have i₂ := eq18886
       grind)
    | exact superpose eq18886 eq274
    | exact resolve eq274 eq18886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18886
  have eq19604 : x = y := by
    first
    | (have i₁ := eq19580 x
       have i₂ := eq274 y x x
       grind)
    | exact superpose eq274 eq19580
    | exact resolve eq19580 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq19580
  have eq19636 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19604
       grind)
    | exact superpose eq19604 eq16
    | exact resolve eq16 eq19604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19604
  have eq19640 : False := by grind
  exact eq19640

/-- `Equation2260`: `x = (x ◇ (y ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation2260 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) = X0 := by
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
  clear eq36
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op (M.op X0 (M.op X1 (M.op X0 X2))) (M.op X3 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 (M.op X0 X2))) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3))) X2
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
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
  have eq74 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq501 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 X0 (M.op (M.op X1 x) (M.op X0 x)) x
       have i₂ := eq14 X0 (M.op X1 x) x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq509 : x = (M.op (M.op x y) (M.op y x)) := by
    first
    | (have i₁ := eq501 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq501
    | (have j0 := eq501 x y
       grind)
    | exact resolve eq501 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : y = (M.op (M.op y x) (M.op x y)) := by
    first
    | (have i₁ := eq501 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq501
    | (have j0 := eq501 y x
       grind)
    | exact resolve eq501 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X1 X0) X2 X1
       have i₂ := eq14 X0 (M.op X1 X0) X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq656 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1801 : ∀ X0 : G, (M.op (M.op x y) (M.op y x)) = (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq516 eq576
    | exact resolve eq576 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq1936 : ∀ X0 : G, x = (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq509 eq1801
    | exact resolve eq1801 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq1801
  have eq11087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11087
    | exact resolve eq11087 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11087
  have eq11099 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq11088
       have r₂ := eq28
       grind)
    | exact resolve eq11088 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11088
  have eq11101 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11099
    | exact resolve eq11099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11099
  have eq11108 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq11101
  have eq11142 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11108
    | exact resolve eq11108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11108
  have eq12323 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq11142 eq113
    | exact resolve eq113 eq11142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11142
  have eq12333 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12323
  have eq12335 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12333
       have r₂ := eq28
       grind)
    | exact resolve eq12333 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12333
  have eq12343 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12335
  have eq12380 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12343
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12343
    | exact resolve eq12343 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12343
  have eq13227 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq12380
       grind)
    | exact superpose eq12380 eq45
    | exact resolve eq45 eq12380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12380
  have eq13247 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq13227
    | exact resolve eq13227 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13227
  have eq14111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13247 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq13247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq14111
    | exact resolve eq14111 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14111
  have eq14125 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14114
       have r₂ := eq28
       grind)
    | exact resolve eq14114 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14114
  have eq14127 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq14125
    | exact resolve eq14125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14125
  have eq14128 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14127
  have eq14136 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14128
  have eq14175 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14136
    | exact resolve eq14136 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14136
  have eq14705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14175 eq13247
    | exact resolve eq13247 eq14175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13247 eq14175
  have eq14711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14705
  have eq14715 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14711
       have r₂ := eq28
       grind)
    | exact resolve eq14711 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14711
  have eq14717 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14715 eq28
    | exact resolve eq28 eq14715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14719 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14715 eq74
    | (have r₁ := eq74
       have r₂ := eq14715
       grind)
    | exact resolve eq74 eq14715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq14715
  have eq14749 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14719
  have eq18035 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14749 eq113
    | exact resolve eq113 eq14749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18056 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq18035
  have eq18070 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18056
       have r₂ := eq14717
       grind)
    | exact resolve eq18056 eq14717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18056
  have eq18081 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq18070
  have eq18128 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18081
    | exact resolve eq18081 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18081
  have eq18275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18128 eq113
    | exact resolve eq113 eq18128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq18128
  have eq18292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq18275
  have eq18296 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18292
       have r₂ := eq28
       grind)
    | exact resolve eq18292 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18292
  have eq18304 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq18296
  have eq18351 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18304
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18304
    | exact resolve eq18304 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18304
  have eq19337 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq18351
       grind)
    | exact superpose eq18351 eq45
    | exact resolve eq45 eq18351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18351
  have eq19363 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq19337
    | exact resolve eq19337 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19337
  have eq19512 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19363 eq14749
    | exact resolve eq14749 eq19363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14749
  have eq19522 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19512
  have eq19530 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19522
       have r₂ := eq14717
       grind)
    | exact resolve eq19522 eq14717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14717 eq19522
  have eq19551 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19530
  have eq19599 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq19551
    | exact resolve eq19551 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19551
  have eq19679 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19599 eq19363
    | exact resolve eq19363 eq19599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19363 eq19599
  have eq19687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19679
  have eq19695 : x = (M.op x y) := by
    first
    | (have r₁ := eq19687
       have r₂ := eq28
       grind)
    | exact resolve eq19687 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19687
  have eq19697 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19695 eq21
    | exact resolve eq21 eq19695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq19703 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq19695 eq73
    | (have r₁ := eq73
       have r₂ := eq19695
       grind)
    | exact resolve eq73 eq19695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq19777 : ∀ X0 : G, x = (M.op x (M.op y (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq19695 eq1936
    | exact resolve eq1936 eq19695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq19779 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq19703
  have eq19830 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19697
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19697
    | exact resolve eq19697 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19697
  have eq19831 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq19830 eq27
    | exact resolve eq27 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25309 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19779
       grind)
    | exact superpose eq19779 eq45
    | exact resolve eq45 eq19779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq25324 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq656 x y
       have i₂ := eq19779
       grind)
    | exact superpose eq19779 eq656
    | (have j0 := eq656 x y
       grind)
    | exact resolve eq656 eq19779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19779
  have eq25326 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq25324
  have eq25334 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25326
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25326
    | exact resolve eq25326 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25326
  have eq25347 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19830 eq25309
    | exact resolve eq25309 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25309
  have eq25350 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25334
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25334
    | exact resolve eq25334 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25334
  have eq25362 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25347
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25347
    | exact resolve eq25347 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25347
  have eq25364 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq25350
    | exact resolve eq25350 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25350
  have eq25374 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19830 eq25362
    | exact resolve eq25362 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25362
  have eq25376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19830 eq25364
    | exact resolve eq25364 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25364
  have eq25383 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq25376
       have r₂ := eq28
       grind)
    | exact resolve eq25376 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25376
  have eq25390 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25383
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25383
    | exact resolve eq25383 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25383
  have eq25397 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25390
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25390
    | exact resolve eq25390 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25390
  have eq25404 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19830 eq25397
    | exact resolve eq25397 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25397
  have eq25486 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq25404
  have eq25555 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19831 eq25486
    | exact resolve eq25486 eq19831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25486
  have eq25978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25555 eq25374
    | exact resolve eq25374 eq25555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25374 eq25555
  have eq25987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq25978
  have eq25989 : x = (M.op y y) := by
    first
    | (have r₁ := eq25987
       have r₂ := eq28
       grind)
    | exact resolve eq25987 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25987
  have eq26006 : (M.op x y) = (k x y) := by grind
  have eq26030 : y = (M.op x x) := by
    first
    | (have i₁ := eq501 y y
       have i₂ := eq25989
       grind)
    | exact superpose eq25989 eq501
    | exact resolve eq501 eq25989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq25989
  have eq26071 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq26006
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26006
    | exact resolve eq26006 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq26006
  have eq26080 : x = (k x y) := by
    first
    | exact superpose eq19695 eq26071
    | exact resolve eq26071 eq19695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19695 eq26071
  have eq26160 : ∀ X0 : G, y = (M.op x (M.op y (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq576 x x x
       have i₂ := eq26030
       grind)
    | exact superpose eq26030 eq576
    | exact resolve eq576 eq26030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq26030
  have eq26179 : x = y := by
    first
    | (have i₁ := eq26160 x
       have i₂ := eq19777 x
       grind)
    | exact superpose eq19777 eq26160
    | exact resolve eq26160 eq19777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19777 eq26160
  have eq26229 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq26179
       grind)
    | exact superpose eq26179 eq25
    | exact resolve eq25 eq26179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq26362 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26229
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26229
    | exact resolve eq26229 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26229
  have eq26421 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19830 eq26362
    | exact resolve eq26362 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26362
  have eq26566 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26421 eq19831
    | exact resolve eq19831 eq26421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19831 eq26421
  have eq26690 : x = (k x x) := by
    first
    | (have i₁ := eq26080
       have i₂ := eq26179
       grind)
    | exact superpose eq26179 eq26080
    | exact resolve eq26080 eq26179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26080 eq26179
  have eq26710 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq656 x x
       have i₂ := eq26690
       grind)
    | exact superpose eq26690 eq656
    | (have j0 := eq656 x x
       grind)
    | exact resolve eq656 eq26690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq26690
  have eq26713 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq26710
  have eq26714 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq26713
  have eq26727 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26714
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26714
    | exact resolve eq26714 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq26714
  have eq26748 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19830 eq26727
    | exact resolve eq26727 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19830 eq26727
  have eq27737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26748 eq26566
    | exact resolve eq26566 eq26748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26566 eq26748
  have eq27738 : False := by grind
  exact eq27738

/-- `Equation2296`: `x = (y ◇ (x ◇ (x ◇ z))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_pxy_pyx_Equation2296 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2296 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2296.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X0 X2))) X0) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op x (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) x))) X1
       have i₂ := eq14 (M.op X0 (M.op X0 X1)) x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq88
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq772 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq69 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq782 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq772 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq784 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq782 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq782 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq782 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq782 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq794 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq784 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq784
    | (have j0 := eq784 X0 X1
       grind)
    | exact resolve eq784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq11613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq11614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq11613
    | exact resolve eq11613 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11613
  have eq11625 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq11614
       have r₂ := eq27
       grind)
    | exact resolve eq11614 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11614
  have eq11627 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq11625
    | exact resolve eq11625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11625
  have eq11642 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq11627 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11627
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq11627
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq11627
       grind)
    | exact resolve eq13 eq11627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11627
  have eq11668 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq11642
  have eq11677 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq11668 eq98
    | exact resolve eq98 eq11668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq11668
  have eq11702 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq11677
    | exact resolve eq11677 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11677
  have eq11705 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq11702
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq11702
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq11702
       have r₂ := eq13 y x
       grind)
    | exact resolve eq11702 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11702
  have eq11715 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq779 x y
       have i₂ := eq11705
       grind)
    | exact superpose eq11705 eq779
    | (have j0 := eq779 x y
       grind)
    | exact resolve eq779 eq11705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11717 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq11705
       grind)
    | exact superpose eq11705 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq11705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11705
  have eq11718 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11717
  have eq11720 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11715
  have eq11723 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11718
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11718
    | exact resolve eq11718 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11718
  have eq11724 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11723
  have eq11726 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11720
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11720
    | exact resolve eq11720 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11720
  have eq11738 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11726
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11726
    | exact resolve eq11726 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11726
  have eq11741 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11738
    | exact resolve eq11738 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11738
  have eq11742 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11741
  have eq11745 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11742
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11742
    | exact resolve eq11742 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11742
  have eq11748 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11745
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11745
    | exact resolve eq11745 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11745
  have eq11761 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq11724
       grind)
    | exact superpose eq11724 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11724
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11724
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11724
       grind)
    | exact resolve eq12 eq11724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11724
  have eq11789 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11761
  have eq11790 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11789
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11789
    | exact resolve eq11789 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11789
  have eq11791 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11790
  have eq11792 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11791
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11791
    | exact resolve eq11791 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11791
  have eq11841 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11748 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11748
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11748
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11748
       grind)
    | exact resolve eq12 eq11748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11748
  have eq11869 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11841
  have eq11870 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11869
    | exact resolve eq11869 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11869
  have eq11871 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11870
  have eq11872 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11871
    | exact resolve eq11871 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11871
  have eq11874 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11792
       grind)
    | exact superpose eq11792 eq44
    | exact resolve eq44 eq11792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq11792
  have eq11894 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11874
    | exact resolve eq11874 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11874
  have eq11936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11894 eq11872
    | exact resolve eq11872 eq11894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11872 eq11894
  have eq11941 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11936
  have eq11943 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11941
       have r₂ := eq27
       grind)
    | exact resolve eq11941 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11941
  have eq11955 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11943 eq51
    | (have r₁ := eq51
       have r₂ := eq11943
       grind)
    | exact resolve eq51 eq11943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq11943
  have eq11980 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11955
  have eq12003 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11980 eq55
    | exact resolve eq55 eq11980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq11980
  have eq12032 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq12003
    | exact resolve eq12003 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12003
  have eq12036 : x = (k x y) := by
    first
    | (have r₁ := eq12032
       have r₂ := eq50
       grind)
    | exact resolve eq12032 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq12032
  have eq12047 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq794 x y
       have i₂ := eq12036
       grind)
    | exact superpose eq12036 eq794
    | (have j0 := eq794 x y
       grind)
    | exact resolve eq794 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq12048 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq779 y x
       have i₂ := eq12036
       grind)
    | exact superpose eq12036 eq779
    | (have j0 := eq779 y x
       grind)
    | exact resolve eq779 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq12050 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq12036
       grind)
    | exact superpose eq12036 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12036
  have eq12051 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq12050
  have eq12053 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12048
  have eq12054 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12047
  have eq12056 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12051
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12051
    | exact resolve eq12051 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12051
  have eq12058 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12053
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12053
    | exact resolve eq12053 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12053
  have eq12059 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12054
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12054
    | exact resolve eq12054 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12054
  have eq12069 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12058
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12058
    | exact resolve eq12058 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12058
  have eq12070 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12059
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12059
    | exact resolve eq12059 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12059
  have eq12072 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12069
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12069
    | exact resolve eq12069 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12069
  have eq12073 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12070
    | exact resolve eq12070 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12070
  have eq12075 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12072
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12072
    | exact resolve eq12072 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12072
  have eq12076 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12073
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12073
    | exact resolve eq12073 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12073
  have eq12078 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12075
    | exact resolve eq12075 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12075
  have eq12079 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12076
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12076
    | exact resolve eq12076 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12076
  have eq12080 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12079
    | exact resolve eq12079 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12079
  have eq12115 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12080 eq27
    | exact resolve eq27 eq12080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12080
  have eq13995 : y = (M.op (M.op y x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59 y x
       have i₂ := eq12056
       grind)
    | exact superpose eq12056 eq59
    | exact resolve eq59 eq12056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23102 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13995
       have i₂ := eq12056
       grind)
    | exact superpose eq12056 eq13995
    | exact resolve eq13995 eq12056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12056 eq13995
  have eq23138 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq23102
  have eq23139 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23138
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23138
    | exact resolve eq23138 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq23138
  have eq23140 : y = (M.op x y) := by grind
  clear eq23139
  have eq23141 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq23140 eq20
    | exact resolve eq20 eq23140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq23140
  have eq23292 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq23141
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23141
    | exact resolve eq23141 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq23141
  have eq23329 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23292 eq26
    | exact resolve eq26 eq23292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq23402 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23292 eq12078
    | exact resolve eq12078 eq23292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12078
  have eq23403 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23292 eq12115
    | (have r₁ := eq12115
       have r₂ := eq23292
       grind)
    | exact resolve eq12115 eq23292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12115 eq23292
  have eq23414 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23403
  have eq23416 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq23402
       have r₂ := eq27
       grind)
    | exact resolve eq23402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23402
  have eq23468 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq23414 eq27
    | exact resolve eq27 eq23414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq24126 : (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23414 eq23329
    | exact resolve eq23329 eq23414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23329 eq23414
  have eq24145 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq23416 eq59
    | exact resolve eq59 eq23416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq24192 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23416 eq24145
    | exact resolve eq24145 eq23416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23416 eq24145
  have eq24608 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq24126 eq24192
    | exact resolve eq24192 eq24126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24126 eq24192
  have eq24609 : False := by grind
  exact eq24609
