import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyx_y_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (k X0 X1))) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X2 X3 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq428 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq456 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq189
       grind)
    | exact superpose eq189 eq40
    | exact resolve eq40 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq457 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq456
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq456
    | exact resolve eq456 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq459 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq457
    | exact resolve eq457 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq459 eq190
    | exact resolve eq190 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq459
  have eq555 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq548
       have r₂ := eq27
       grind)
    | exact resolve eq548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq623 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq555 eq13
    | exact resolve eq13 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq633 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq623
  have eq642 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq635
       have i₂ := eq633 x
       grind)
    | exact superpose eq633 eq635
    | exact resolve eq635 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq667 : (τ (σ y)) = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq642 eq98
    | exact resolve eq98 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq642
  have eq674 : y = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq667
    | exact resolve eq667 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq667
  have eq675 : y = (k x x) := by grind
  clear eq674
  have eq681 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq40
    | exact resolve eq40 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq684 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq681
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq681
    | exact resolve eq681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq687 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq684
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq684
    | exact resolve eq684 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq1213 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (k x x))) := by
    intro X0
    first
    | (have i₁ := eq175 X0 x
       have i₂ := eq633 x
       grind)
    | exact superpose eq633 eq175
    | exact resolve eq175 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1216 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq176 X0 sF2
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq176
    | exact resolve eq176 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1279 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq687 eq1216
    | exact resolve eq1216 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1280 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1213 X0
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq1213
    | exact resolve eq1213 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1328 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1280 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1280
    | (have j0 := eq1280 x
       grind)
    | exact resolve eq1280 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1280
  have eq1339 : x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1328
       have i₂ := eq633 sF0
       grind)
    | exact superpose eq633 eq1328
    | exact resolve eq1328 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1343 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1339 eq42
    | exact resolve eq42 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq1346 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1343
    | exact resolve eq1343 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1343
  have eq1349 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1346
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1346
    | exact resolve eq1346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq2017 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1279 eq177
    | exact resolve eq177 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1279
  have eq3162 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1349 eq185
    | (have j0 := eq185 (σ (M.op x y)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq185 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq3228 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2017 eq3162
    | exact resolve eq3162 eq2017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017 eq3162
  have eq3288 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3228 X0
       have i₂ := eq633 sF1
       grind)
    | exact superpose eq633 eq3228
    | (have j0 := eq3228 X0
       grind)
    | exact resolve eq3228 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228
  have eq3306 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1349 eq3288
    | (have j0 := eq3288 X0
       grind)
    | exact resolve eq3288 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288
  have eq3725 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3306 sF1
       have i₂ := eq633 sF1
       grind)
    | exact superpose eq633 eq3306
    | exact resolve eq3306 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3306
  have eq3763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1349 eq3725
    | exact resolve eq3725 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349 eq3725
  have eq3767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq3763
    | exact resolve eq3763 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3763
  have eq3769 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3767
       have r₂ := eq27
       grind)
    | exact resolve eq3767 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3767
  have eq3772 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq3769 eq86
    | exact resolve eq86 eq3769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq3776 : (k (M.op x y) x) = (τ (k (σ x) (σ x))) := by
    first
    | exact superpose eq3769 eq132
    | exact resolve eq132 eq3769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq3784 : (k (M.op x y) x) = (k x (τ (σ x))) := by
    first
    | exact superpose eq91 eq3776
    | exact resolve eq3776 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq3776
  have eq3787 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq3772 X0
       have i₂ := eq428 X0 sF2
       grind)
    | exact superpose eq428 eq3772
    | exact resolve eq3772 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq3772
  have eq3791 : (k x x) = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq3784
    | exact resolve eq3784 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3784
  have eq3794 : ∀ X0 : G, (k X0 x) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq3787
    | exact resolve eq3787 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3787
  have eq3797 : y = (k (M.op x y) x) := by
    first
    | (have i₁ := eq3791
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq3791
    | exact resolve eq3791 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq3791
  have eq3800 : y = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3797
       have i₂ := eq3794 sF0
       grind)
    | exact superpose eq3794 eq3797
    | exact resolve eq3797 eq3794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3794 eq3797
  have eq3803 : x = y := by
    first
    | exact superpose eq1339 eq3800
    | exact resolve eq3800 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq3800
  have eq3806 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3803
       grind)
    | exact superpose eq3803 eq24
    | exact resolve eq24 eq3803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3803
  have eq3845 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3806
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3806
    | exact resolve eq3806 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3806
  have eq3949 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3845 eq26
    | exact resolve eq26 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4034 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3949
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq3949
    | exact resolve eq3949 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq3949
  have eq4059 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq687 eq4034
    | exact resolve eq4034 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq4034
  have eq4068 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3845 eq4059
    | exact resolve eq4059 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845 eq4059
  have eq4069 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4068 eq27
    | exact resolve eq27 eq4068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4068
  have eq4125 : False := by grind
  exact eq4125

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxx_pyx_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq66 : x ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq89
    | exact resolve eq89 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
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
  have eq93 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (M.op x y) = (M.op y x) ∨ (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
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
  have eq100 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq105 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X1)) ≠ X0 ∨ (M.op X2 (M.op X3 X0)) = (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X1)) ∨ (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X2 (M.op X3 X0))
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X0 X1) (M.op X2 (M.op X3 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X3)) ≠ X0 ∨ (M.op X0 X3) = X0 ∨ (k (M.op X1 (M.op X2 X0)) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X2 (M.op X3 X0)) (M.op X0 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X3 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq114 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq114 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq114 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq115 (σ X0)
       grind)
    | exact superpose eq115 eq10
    | exact resolve eq10 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq43
    | exact resolve eq43 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq119 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq115 y
       grind)
    | exact superpose eq115 eq76
    | exact resolve eq76 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq120 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq115 sF2
       grind)
    | exact superpose eq115 eq49
    | exact resolve eq49 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq121 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq120
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq120
    | exact resolve eq120 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq115 sF3
       grind)
    | exact superpose eq115 eq119
    | exact resolve eq119 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq115 sF2
       grind)
    | exact superpose eq115 eq118
    | exact resolve eq118 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq124 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq117
    | exact resolve eq117 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq130 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq105
       have i₂ := eq115 sF3
       grind)
    | exact superpose eq115 eq105
    | exact resolve eq105 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq131 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq130
       have i₂ := eq115 y
       grind)
    | exact superpose eq115 eq130
    | exact resolve eq130 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq144 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq115 sF1
       grind)
    | exact superpose eq115 eq141
    | exact resolve eq141 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq147 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq115 sF0
       grind)
    | exact superpose eq115 eq144
    | exact resolve eq144 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq259 : ∀ X2 X3 : G, (M.op x y) = (M.op x (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X2 X3
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq115 (τ X0)
       grind)
    | exact superpose eq115 eq34
    | exact resolve eq34 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq339 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq328 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq328
    | exact resolve eq328 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq341 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq339 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq339
    | exact resolve eq339 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq542 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op X2 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2 (σ X0)
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq14
    | exact resolve eq14 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1 X2
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq14
    | exact resolve eq14 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X0) x
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq56
    | exact resolve eq56 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq332
    | (have j0 := eq332 X0 (M.op x y)
       grind)
    | exact resolve eq332 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq695 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
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
  have eq697 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
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
  clear eq52 eq55
  have eq889 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq341 X0
       grind)
    | exact superpose eq341 eq16
    | exact resolve eq16 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq1044 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op X2 (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (τ X0) X1 X2 (τ X0)
       have i₂ := eq889 X0
       grind)
    | exact superpose eq889 eq14
    | exact resolve eq14 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X2 : G, (M.op x y) ≠ (M.op y (M.op (M.op x y) X2)) ∨ (M.op x y) = (M.op (M.op x y) X2) ∨ (M.op x y) = (k y (M.op (M.op x y) X2)) := by
    intro X2
    first
    | exact superpose eq53 eq113
    | (have j0 := eq113 (M.op x y) x X2 X2
       grind)
    | (have r₁ := eq113 y y X2 (M.op x y)
       have r₂ := eq53 (M.op X2 y) y
       grind)
    | exact resolve eq113 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1108 : ∀ X0 X1 X2 X3 : G, X0 ≠ X2 ∨ (M.op X2 (M.op X3 X0)) = X2 ∨ (k (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X3 X0))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X2 X0 X1 (M.op X3 X0)
       have i₂ := eq14 X0 (M.op X1 X2) X2 X3
       grind)
    | exact superpose eq14 eq113
    | (have j0 := eq113 X2 X0 X1 (M.op X3 X0)
       grind)
    | (have r₁ := eq113 X0 X0 X2 (M.op X3 X0)
       have r₂ := eq14 X0 (M.op X2 X0) X0 X3
       grind)
    | exact resolve eq113 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1171 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1184 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1171 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq1190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1184 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1184
    | (have j0 := eq1184 X0 X1
       grind)
    | exact resolve eq1184 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1191 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1427 : ∀ X2 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (M.op (σ x) (σ y)) X2)) ∨ (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X2)) ∨ (M.op (σ y) (M.op (M.op (σ x) (σ y)) X2)) = (k (M.op (M.op (σ x) (σ y)) X2) (σ y)) := by
    intro X2
    first
    | exact superpose eq54 eq112
    | (have r₁ := eq112 (σ y) (M.op (σ x) (σ y)) (σ y) x
       have r₂ := eq54 (M.op x (σ y)) (σ y)
       grind)
    | exact resolve eq112 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1620 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op X2 (M.op X3 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq838 X3 (σ X0) (σ X0) X1 X2
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq838
    | exact resolve eq838 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4184 : (M.op x y) ≠ (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq50 eq1083
    | exact resolve eq1083 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4196 : ∀ X0 X1 X2 : G, (M.op x y) ≠ (M.op y X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op X1 (M.op X2 X0))) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1083 (M.op X0 (M.op X1 X2))
       have i₂ := eq838 X0 X1 X2 y sF0
       grind)
    | exact superpose eq838 eq1083
    | (have j0 := eq1083 (M.op X1 (M.op X2 X0))
       grind)
    | exact resolve eq1083 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq6349 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X2 X0)) (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1108 X0 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq9107 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq51 eq1427
    | exact resolve eq1427 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq10364 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1191 X0 X1
       have j1 := eq1183 X1 X0
       grind)
    | (have r₁ := eq1191 X1 X0
       have r₂ := eq1183 X0 X1
       grind)
    | (have r₁ := eq1191 X1 X1
       have r₂ := eq1183 X1 X1
       grind)
    | exact resolve eq1191 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183 eq1191
  have eq10665 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10364 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10364
    | exact resolve eq10364 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10755 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10364 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10364
    | exact resolve eq10364 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10862 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (σ X1)) = (M.op X2 (M.op X3 (M.op X4 (σ (k X0 X1))))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq838 X4 (σ X0) (σ X1) X2 X3
       have i₂ := eq10364 X0 X1
       grind)
    | exact superpose eq10364 eq838
    | (have j1 := eq10364 X0 X1
       grind)
    | exact resolve eq838 eq10364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq10364
  have eq10876 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10755 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq10755
    | (have j0 := eq10755 X0 X1
       grind)
    | exact resolve eq10755 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq10755
  have eq10884 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10665 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10665
    | (have j0 := eq10665 X0 X1
       grind)
    | exact resolve eq10665 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq10665
  have eq15499 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq542 X0 (σ X0) X1
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq542
    | exact resolve eq542 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq542
  have eq16163 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X2) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq562 (M.op X2 (M.op x X2)) X1
       have i₂ := eq14 X2 (M.op x X2) X2 x
       grind)
    | exact superpose eq14 eq562
    | exact resolve eq562 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22268 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X0)) X1) (σ (M.op (τ X0) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq562 (M.op (τ X0) (τ (M.op X0 X0))) X1
       have i₂ := eq1044 X0 (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact superpose eq1044 eq562
    | exact resolve eq562 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq22309 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op (τ X0) (τ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22268 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq22268
    | exact resolve eq22268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22268
  have eq22759 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ X0) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15499 (M.op X2 (M.op x X2)) X1
       have i₂ := eq14 X2 (M.op x X2) X2 x
       grind)
    | exact superpose eq14 eq15499
    | exact resolve eq15499 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22763 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (M.op (σ (τ X0)) (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15499 (M.op (τ X0) (τ (M.op X0 X0))) X1
       have i₂ := eq1044 X0 (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact superpose eq1044 eq15499
    | exact resolve eq15499 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq15499
  have eq22853 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22763 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq22763
    | exact resolve eq22763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22763
  have eq23212 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x (M.op X1 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16163 x X1 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16163
    | (have j0 := eq16163 x X1 X0
       grind)
    | exact resolve eq16163 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16163
  have eq23455 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x (M.op X0 x)))) := by
    intro X0
    first
    | exact superpose eq26 eq23212
    | (have j0 := eq23212 (σ y) X0
       grind)
    | exact resolve eq23212 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23493 : ∀ X0 X1 : G, (σ (M.op x (M.op X0 x))) = (M.op (σ (M.op (M.op x (M.op X0 x)) (M.op x (M.op X0 x)))) (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq23212 eq543
    | exact resolve eq543 eq23212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq23212
  have eq23533 : ∀ X0 X1 : G, (σ (M.op x (M.op X0 x))) = (M.op (σ x) (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq23493 X0 X1
       have i₂ := eq14 x (M.op X0 x) x X0
       grind)
    | exact superpose eq14 eq23493
    | exact resolve eq23493 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23493
  have eq23536 : ∀ X0 X1 : G, (σ (M.op x (M.op X0 x))) = (M.op (σ x) (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq23533 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23533
    | (have j0 := eq23533 X0 X1
       grind)
    | exact resolve eq23533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23533
  have eq23884 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (τ (M.op (σ x) (M.op X0 (σ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op x (M.op X1 x))
       have i₂ := eq23536 X1 X0
       grind)
    | exact superpose eq23536 eq16
    | exact resolve eq16 eq23536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24283 : ∀ X0 : G, x = (M.op (M.op x y) (τ (M.op (σ x) (M.op X0 (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq50 x x
       have i₂ := eq23884 X0 x
       grind)
    | exact superpose eq23884 eq50
    | exact resolve eq50 eq23884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24431 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k (τ (M.op (σ x) (M.op X0 (σ x)))) (M.op x y)) = (M.op (τ (M.op (σ x) (M.op X0 (σ x)))) (τ (M.op (σ x) (M.op X0 (σ x))))) := by
    intro X0
    first
    | exact superpose eq24283 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq24283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24283
  have eq24467 : ∀ X0 : G, (k (τ (M.op (σ x) (M.op X0 (σ x)))) (M.op x y)) = (τ (M.op (M.op (σ x) (M.op X0 (σ x))) (M.op (σ x) (M.op X0 (σ x))))) ∨ x ≠ (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24431 X0
       have i₂ := eq889 (M.op sF2 (M.op X0 sF2))
       grind)
    | exact superpose eq889 eq24431
    | exact resolve eq24431 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq24431
  have eq24472 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op (σ x) (M.op X0 (σ x)))) (M.op x y)) ∨ x ≠ (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24467 x
       have i₂ := eq14 sF2 (M.op x sF2) sF2 x
       grind)
    | exact superpose eq14 eq24467
    | exact resolve eq24467 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24467
  have eq24476 : ∀ X0 : G, (τ (σ x)) = (τ (k (M.op (σ x) (M.op X0 (σ x))) (σ (M.op x y)))) ∨ x ≠ (M.op x y) := by
    intro X0
    first
    | exact superpose eq604 eq24472
    | exact resolve eq24472 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24472
  have eq24477 : ∀ X0 : G, x ≠ (M.op x y) ∨ x = (τ (k (M.op (σ x) (M.op X0 (σ x))) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq28 eq24476
    | exact resolve eq24476 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24476
  have eq30297 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (σ (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22759 X0 X1 x
       have i₂ := eq22759 X0 X2 x
       grind)
    | exact superpose eq22759 eq22759
    | exact resolve eq22759 eq22759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22759
  have eq32578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq32578
    | exact resolve eq32578 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32578
  have eq32590 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq32579
       have r₂ := eq27
       grind)
    | exact resolve eq32579 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32579
  have eq32594 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq32590
    | exact resolve eq32590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32590
  have eq32654 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  have eq45199 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32594 eq9107
    | (have r₁ := eq9107
       have r₂ := eq32594
       grind)
    | exact resolve eq9107 eq32594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9107 eq32594
  have eq45200 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq45199
  have eq45201 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq45200
       have r₂ := eq32654
       grind)
    | exact resolve eq45200 eq32654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32654 eq45200
  have eq92077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq45201 eq92
    | exact resolve eq92 eq45201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq45201
  have eq92102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq92077
  have eq92107 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq92102
       have r₂ := eq27
       grind)
    | exact resolve eq92102 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92102
  have eq92133 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq92107 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq92107
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq92107
       grind)
    | exact resolve eq13 eq92107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92107
  have eq92177 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq92133
  have eq93407 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq92177 eq60
    | exact resolve eq60 eq92177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92177
  have eq93427 : (k x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq121 eq93407
    | exact resolve eq93407 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93407
  have eq93430 : (k x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq93427
       have r₂ := eq13 x y
       grind)
    | exact resolve eq93427 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93427
  have eq93446 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq93430
       grind)
    | exact superpose eq93430 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq93430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93430
  have eq93447 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq93446
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93446
    | exact resolve eq93446 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93446
  have eq93462 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq93447
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93447
    | exact resolve eq93447 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93447
  have eq93463 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq93462
  have eq93666 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq93463
       grind)
    | exact superpose eq93463 eq50
    | exact resolve eq50 eq93463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93463
  have eq97705 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq93666 eq259
    | exact resolve eq259 eq93666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq93666
  have eq97781 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq97705
  have eq97839 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq123
       have i₂ := eq97781
       grind)
    | exact superpose eq97781 eq123
    | exact resolve eq123 eq97781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq97866 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq50 X0 x
       have i₂ := eq97781
       grind)
    | exact superpose eq97781 eq50
    | exact resolve eq50 eq97781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97781
  have eq97985 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq97839
    | exact resolve eq97839 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97839
  have eq98732 : x = (σ (M.op (τ (M.op x y)) (τ (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq97866 x
       have i₂ := eq22853 sF0 x
       grind)
    | exact superpose eq22853 eq97866
    | exact resolve eq97866 eq22853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22853
  have eq98761 : ∀ X1 : G, (σ x) = (σ (M.op (M.op x y) (M.op X1 (M.op x y)))) ∨ y = (M.op y x) := by
    intro X1
    first
    | exact superpose eq97866 eq30297
    | exact resolve eq30297 eq97866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30297 eq97866
  have eq98873 : ∀ X1 : G, (σ x) = (σ (M.op (M.op x y) (M.op X1 (M.op x y)))) ∨ y = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq98761 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq98761
    | (have j0 := eq98761 X1
       grind)
    | exact resolve eq98761 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98761
  have eq105325 : ∀ X1 : G, (k (σ x) X1) = (M.op (σ x) X1) ∨ (M.op X1 (σ x)) = X1 ∨ y = (M.op y x) := by
    intro X1
    first
    | exact superpose eq98873 eq10876
    | (have j0 := eq10876 X1 x
       grind)
    | exact resolve eq10876 eq98873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105326 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq98873 eq10884
    | (have j0 := eq10884 X0 x
       grind)
    | exact resolve eq10884 eq98873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98873
  have eq136143 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (M.op X0 x) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq98732 eq10876
    | exact resolve eq10876 eq98732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10876 eq98732
  have eq229568 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq105326 eq98
    | (have j1 := eq105326 (σ y)
       grind)
    | exact resolve eq98 eq105326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105326
  have eq229806 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq229568
    | exact resolve eq229568 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229568
  have eq239284 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq136143 y
       grind)
    | exact superpose eq136143 eq44
    | (have j1 := eq136143 y
       grind)
    | exact resolve eq44 eq136143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq136143
  have eq239369 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq239284
  have eq239437 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq239369
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq239369
    | exact resolve eq239369 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239369
  have eq239562 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq239437
    | exact resolve eq239437 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239437
  have eq239618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq239562 eq105325
    | (have j0 := eq105325 (σ y)
       grind)
    | exact resolve eq105325 eq239562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105325 eq239562
  have eq239625 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq239618
  have eq239640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq239625
    | exact resolve eq239625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239625
  have eq239656 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq239640
       have r₂ := eq27
       grind)
    | exact resolve eq239640 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239640
  have eq239763 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq239656 eq229806
    | exact resolve eq229806 eq239656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229806
  have eq239773 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq239656 eq51
    | exact resolve eq51 eq239656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq239803 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq239656 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq239656
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq239656
       grind)
    | exact resolve eq13 eq239656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239656
  have eq239858 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq239803
  have eq239885 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq239763
  have eq239929 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq697 eq239773
    | (have j0 := eq239773 (σ x)
       grind)
    | exact resolve eq239773 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq239773
  have eq239931 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq239885
    | exact resolve eq239885 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq239885
  have eq242207 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq239858 eq60
    | exact resolve eq60 eq239858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq239858
  have eq242244 : (k x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq121 eq242207
    | exact resolve eq242207 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq242207
  have eq242247 : (k x y) = (M.op x x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq242244
       have r₂ := eq13 x y
       grind)
    | exact resolve eq242244 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242244
  have eq242275 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (M.op X2 (σ (M.op x x))))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10862 x y X0 X1 X2
       have i₂ := eq242247
       grind)
    | exact superpose eq242247 eq10862
    | (have j0 := eq10862 x y X2 x x
       grind)
    | exact resolve eq10862 eq242247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242247
  have eq242278 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq242275 X0 x x
       have i₂ := eq1620 x X0 x x
       grind)
    | exact superpose eq1620 eq242275
    | exact resolve eq242275 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242275
  have eq242297 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq242278 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq242278
    | (have j0 := eq242278 X0
       grind)
    | exact resolve eq242278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242278
  have eq242302 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq242297 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq242297
    | (have j0 := eq242297 X0
       grind)
    | exact resolve eq242297 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242297
  have eq242307 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq242302 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq242302
    | (have j0 := eq242302 X0
       grind)
    | exact resolve eq242302 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242302
  have eq242310 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq242307 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq242307
    | (have j0 := eq242307 X0
       grind)
    | exact resolve eq242307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242307
  have eq259417 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq270 eq242310
    | exact resolve eq242310 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq262174 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op x (M.op X0 x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq259417 eq23536
    | exact resolve eq23536 eq259417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259417
  have eq267467 : y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq239931
       grind)
    | exact superpose eq239931 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq239931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267473 : y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq267467
  have eq267480 : (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq267473
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq267473
    | exact resolve eq267473 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267473
  have eq267502 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq267480
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq267480
    | exact resolve eq267480 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267480
  have eq493103 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4184
       have i₂ := eq267502
       grind)
    | exact superpose eq267502 eq4184
    | (have r₁ := eq4184
       have r₂ := eq267502
       grind)
    | exact resolve eq4184 eq267502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4184
  have eq493271 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq267502
  have eq493281 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq493103
  have eq493282 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq493281
  have eq564182 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq239931
       have i₂ := eq493282
       grind)
    | exact superpose eq493282 eq239931
    | exact resolve eq239931 eq493282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239931 eq493282
  have eq564213 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq564182
  have eq564244 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq564213
       have r₂ := eq493271
       grind)
    | exact resolve eq564213 eq493271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493271 eq564213
  have eq565373 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq564244
       grind)
    | exact superpose eq564244 eq100
    | exact resolve eq100 eq564244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565387 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23455 y
       have i₂ := eq564244
       grind)
    | exact superpose eq564244 eq23455
    | exact resolve eq23455 eq564244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23455
  have eq565388 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23536 y X0
       have i₂ := eq564244
       grind)
    | exact superpose eq564244 eq23536
    | exact resolve eq23536 eq564244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565394 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq262174 y
       have i₂ := eq564244
       grind)
    | exact superpose eq564244 eq262174
    | exact resolve eq262174 eq564244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262174
  have eq565451 : ∀ X0 : G, x = (k (M.op x (M.op X0 x)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6349 x y x
       have i₂ := eq564244
       grind)
    | exact superpose eq564244 eq6349
    | exact resolve eq6349 eq564244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6349 eq564244
  have eq565492 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq565373
  have eq565503 : ∀ X0 : G, x = (k (M.op x (M.op X0 x)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq565451 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq565451
    | (have j0 := eq565451 X0
       grind)
    | exact resolve eq565451 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565451
  have eq565524 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq565394
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq565394
    | exact resolve eq565394 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565394
  have eq565529 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq565388 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq565388
    | (have j0 := eq565388 X0
       grind)
    | exact resolve eq565388 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565388
  have eq565530 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq565387
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq565387
    | exact resolve eq565387 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565387
  have eq565536 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq565492
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq565492
    | exact resolve eq565492 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565492
  have eq565543 : ∀ X0 : G, x = (M.op x y) ∨ x = (k (M.op x (M.op X0 x)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq565503 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq565503
    | (have j0 := eq565503 X0
       grind)
    | exact resolve eq565503 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565503
  have eq565544 : ∀ X0 : G, x = (k (M.op x (M.op X0 x)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq565543 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565543
  have eq565556 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq565524
    | exact resolve eq565524 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565524
  have eq565559 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq565529
    | (have j0 := eq565529 X0
       grind)
    | exact resolve eq565529 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565529
  have eq565560 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq565530
    | exact resolve eq565530 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565530
  have eq567560 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq565560 eq695
    | exact resolve eq695 eq565560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq565560
  have eq604747 : ∀ X0 : G, x = (k (τ (M.op (σ x) (M.op X0 (σ x)))) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq565544 x
       have i₂ := eq23884 X0 x
       grind)
    | exact superpose eq23884 eq565544
    | exact resolve eq565544 eq23884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23884 eq565544
  have eq604815 : ∀ X0 : G, x = (τ (k (M.op (σ x) (M.op X0 (σ x))) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq604 eq604747
    | exact resolve eq604747 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq604747
  have eq604835 : ∀ X0 : G, x = (τ (k (M.op (σ x) (M.op X0 (σ x))) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq604815 X0
       have j1 := eq24477 X0
       grind)
    | (have r₁ := eq604815 X0
       have r₂ := eq24477 X0
       grind)
    | exact resolve eq604815 eq24477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24477 eq604815
  have eq604912 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (M.op X0 (σ x))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq604835 eq15
    | exact resolve eq15 eq604835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604835
  have eq605319 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (M.op X0 (σ x))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq604912 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq604912
    | (have j0 := eq604912 X0
       grind)
    | exact resolve eq604912 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604912
  have eq605383 : ∀ X0 : G, (σ x) = (k (σ (M.op x (M.op X0 x))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23536 eq605319
    | exact resolve eq605319 eq23536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605319
  have eq605429 : ∀ X0 : G, (σ x) = (σ (k (M.op x (M.op X0 x)) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq605383
    | exact resolve eq605383 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq605383
  have eq605929 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq605429 eq10884
    | (have j0 := eq10884 X0 x
       grind)
    | exact resolve eq10884 eq605429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10884
  have eq632164 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq605929 eq98
    | (have j1 := eq605929 (σ y)
       grind)
    | exact resolve eq98 eq605929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632175 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq605929 eq565536
    | (have j1 := eq605929 (σ y)
       grind)
    | exact resolve eq565536 eq605929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565536 eq605929
  have eq632420 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq632175
  have eq632484 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq632420
    | exact resolve eq632420 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632420
  have eq632485 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq632484
  have eq632504 : (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq632164
    | exact resolve eq632164 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632164
  have eq632505 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq632504
  have eq633060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq632485 eq565559
    | exact resolve eq565559 eq632485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632485
  have eq633174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq633060
  have eq633218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq633174
    | exact resolve eq633174 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633174
  have eq633249 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq633218
       have r₂ := eq27
       grind)
    | exact resolve eq633218 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633218
  have eq936226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq565556 eq565559
    | exact resolve eq565559 eq565556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565556 eq565559
  have eq936403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq936226
  have eq936470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq936403
    | exact resolve eq936403 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936403
  have eq936520 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq936470
       have r₂ := eq27
       grind)
    | exact resolve eq936470 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936470
  have eq936568 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq936520 eq54
    | exact resolve eq54 eq936520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq936520
  have eq937141 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq936568 eq567560
    | exact resolve eq567560 eq936568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567560 eq936568
  have eq937312 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq937141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937141
  have eq940971 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq937312 eq131
    | exact resolve eq131 eq937312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937312
  have eq962325 : (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq940971 eq632505
    | exact resolve eq632505 eq940971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632505 eq940971
  have eq962758 : (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq962325
  have eq962829 : (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq962758
       have r₂ := eq66
       grind)
    | exact resolve eq962758 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq962758
  have eq962895 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq962829
       grind)
    | exact superpose eq962829 eq75
    | exact resolve eq75 eq962829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq962957 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (M.op X2 (σ (M.op y y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10862 y x X0 X1 X2
       have i₂ := eq962829
       grind)
    | exact superpose eq962829 eq10862
    | (have j0 := eq10862 y x X2 x x
       grind)
    | exact resolve eq10862 eq962829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10862 eq962829
  have eq962973 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq962957 X0 x x
       have i₂ := eq1620 y X0 x x
       grind)
    | exact superpose eq1620 eq962957
    | exact resolve eq962957 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620 eq962957
  have eq963028 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq962895
       have i₂ := eq122
       grind)
    | exact superpose eq122 eq962895
    | exact resolve eq962895 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962895
  have eq963034 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq962973 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq962973
    | (have j0 := eq962973 X0
       grind)
    | exact resolve eq962973 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962973
  have eq963074 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq963028
       have r₂ := eq67
       grind)
    | exact resolve eq963028 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq963028
  have eq963080 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq963034 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq963034
    | (have j0 := eq963034 X0
       grind)
    | exact resolve eq963034 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963034
  have eq963120 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq963080 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq963080
    | (have j0 := eq963080 X0
       grind)
    | exact resolve eq963080 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963080
  have eq963155 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq963120 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq963120
    | (have j0 := eq963120 X0
       grind)
    | exact resolve eq963120 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963120
  have eq963191 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq963155
    | (have j0 := eq963155 X0
       grind)
    | exact resolve eq963155 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963155
  have eq963192 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq963191 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963191
  have eq963299 : (k y x) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq963074 eq98
    | exact resolve eq98 eq963074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq963361 : (k y x) = (M.op y y) := by
    first
    | exact superpose eq131 eq963299
    | exact resolve eq963299 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq963299
  have eq963751 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq963192
    | (have j0 := eq963192 (σ x)
       grind)
    | exact resolve eq963192 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963192
  have eq964557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq963751 eq97985
    | exact resolve eq97985 eq963751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964939 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq964557
       have r₂ := eq27
       grind)
    | exact resolve eq964557 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964557
  have eq964965 : ∀ X0 X1 : G, y ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op X1 x))) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op X0 (M.op X1 x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq4196 x X0 X1
       have i₂ := eq964939
       grind)
    | exact superpose eq964939 eq4196
    | (have j0 := eq4196 x X0 X1
       grind)
    | exact resolve eq4196 eq964939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196
  have eq964989 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq605429 y
       have i₂ := eq964939
       grind)
    | exact superpose eq964939 eq605429
    | exact resolve eq605429 eq964939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605429
  have eq965000 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq56 x y x
       have i₂ := eq964939
       grind)
    | exact superpose eq964939 eq56
    | exact resolve eq56 eq964939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq964939
  have eq965144 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq964989
  have eq965199 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq965144
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq965144
    | exact resolve eq965144 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965144
  have eq965214 : ∀ X0 X1 : G, x = (M.op x y) ∨ y ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op X0 (M.op X1 x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq964965
    | (have j0 := eq964965 X0 X1
       grind)
    | exact resolve eq964965 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964965
  have eq965244 : (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq965199
       have i₂ := eq115 sF0
       grind)
    | exact superpose eq115 eq965199
    | exact resolve eq965199 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq965199
  have eq965253 : ∀ X0 X1 : G, x = (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op X0 (M.op X1 x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq965214 X0 X1
       grind)
    | (have r₁ := eq965214 X0 X1
       have r₂ := eq633249
       grind)
    | exact resolve eq965214 eq633249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633249 eq965214
  have eq965262 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq147 eq965244
    | exact resolve eq965244 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq965244
  have eq965263 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50 eq965253
    | exact resolve eq965253 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq965253
  have eq965266 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq965263
       have i₂ := eq963361
       grind)
    | exact superpose eq963361 eq965263
    | exact resolve eq965263 eq963361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963361 eq965263
  have eq966362 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op (τ (σ (M.op x y))) (τ (σ x))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq965262 eq22309
    | exact resolve eq22309 eq965262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22309
  have eq966414 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op (τ (σ (M.op x y))) x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq966362
    | exact resolve eq966362 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq966362
  have eq966450 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op (M.op x y) x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq966414
    | exact resolve eq966414 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq966414
  have eq998893 : y = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq965000 y
       have i₂ := eq965266
       grind)
    | exact superpose eq965266 eq965000
    | exact resolve eq965000 eq965266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965000 eq965266
  have eq999088 : y = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq998893
  have eq1002064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq999088 eq966450
    | exact resolve eq966450 eq999088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966450 eq999088
  have eq1002313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1002064
  have eq1002379 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1002313
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1002313
    | exact resolve eq1002313 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002313
  have eq1002420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1002379
    | exact resolve eq1002379 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002379
  have eq1002428 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1002420
       have r₂ := eq27
       grind)
    | exact resolve eq1002420 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002420
  have eq1002431 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1002428 eq27
    | exact resolve eq27 eq1002428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1002576 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1002428 eq239929
    | exact resolve eq239929 eq1002428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239929 eq1002428
  have eq1237598 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1002576 eq97985
    | exact resolve eq97985 eq1002576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97985 eq1002576
  have eq1238094 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1237598
  have eq1238192 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1238094
       have r₂ := eq1002431
       grind)
    | exact resolve eq1238094 eq1002431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002431 eq1238094
  have eq1238242 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq1238192
       grind)
    | exact superpose eq1238192 eq100
    | exact resolve eq100 eq1238192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1238261 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23536 y X0
       have i₂ := eq1238192
       grind)
    | exact superpose eq1238192 eq23536
    | exact resolve eq23536 eq1238192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23536
  have eq1238460 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1238242
  have eq1238521 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1238261 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1238261
    | (have j0 := eq1238261 X0
       grind)
    | exact resolve eq1238261 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1238261
  have eq1238529 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq963074 eq1238460
    | exact resolve eq1238460 eq963074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963074 eq1238460
  have eq1238574 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq1238521
    | (have j0 := eq1238521 X0
       grind)
    | exact resolve eq1238521 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238521
  have eq1238579 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1238529
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1238529
    | exact resolve eq1238529 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238529
  have eq1263708 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1238579 eq242310
    | exact resolve eq242310 eq1238579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238579
  have eq1263911 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1263708
  have eq1267191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1263911 eq1238574
    | exact resolve eq1238574 eq1263911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263911
  have eq1267360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1267191
  have eq1267446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1267360
    | exact resolve eq1267360 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267360
  have eq1267505 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1267446
       have r₂ := eq27
       grind)
    | exact resolve eq1267446 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267446
  have eq1267576 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1267505 eq264
    | exact resolve eq264 eq1267505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq1267505
  have eq1272225 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1267576 x
       have i₂ := eq1238192
       grind)
    | exact superpose eq1238192 eq1267576
    | exact resolve eq1267576 eq1238192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238192 eq1267576
  have eq1272691 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1272225
  have eq1272944 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq1272691
       grind)
    | exact superpose eq1272691 eq122
    | exact resolve eq122 eq1272691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq1272691
  have eq1273342 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1272944
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1272944
    | exact resolve eq1272944 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1272944
  have eq1273611 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1273342 eq242310
    | exact resolve eq242310 eq1273342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242310 eq1273342
  have eq1273813 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1273611
  have eq1277896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1273813 eq1238574
    | exact resolve eq1238574 eq1273813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238574 eq1273813
  have eq1278065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1277896
  have eq1278144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1278065
    | exact resolve eq1278065 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1278065
  have eq1278200 : x = (M.op x y) := by
    first
    | (have r₁ := eq1278144
       have r₂ := eq27
       grind)
    | exact resolve eq1278144 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278144
  have eq1280294 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1278200 eq20
    | exact resolve eq20 eq1278200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1278200
  have eq1281264 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1280294
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1280294
    | exact resolve eq1280294 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1280294
  have eq1282037 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1281264 eq963751
    | exact resolve eq963751 eq1281264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963751
  have eq1282225 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1282037
       have r₂ := eq27
       grind)
    | exact resolve eq1282037 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282037
  have eq1283968 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1282225 eq965262
    | exact resolve eq965262 eq1282225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965262 eq1282225
  have eq1284294 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1283968
  have eq1284421 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1281264 eq1284294
    | exact resolve eq1284294 eq1281264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281264 eq1284294
  have eq1284551 : False := by grind
  exact eq1284551

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq501 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq531 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq501 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq532 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq531 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq540 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq532 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq532 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq532 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq550 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq540
    | (have j0 := eq540 X0 X1
       grind)
    | exact resolve eq540 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq551 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq550 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq556 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq551 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq551
    | exact resolve eq551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq551 x y
       grind)
    | exact superpose eq551 eq16
    | exact resolve eq16 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq660 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq556 X0 (τ X1)
       grind)
    | exact superpose eq556 eq17
    | exact resolve eq17 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq556
  have eq676 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq660
    | exact resolve eq660 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq683 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq676
    | exact resolve eq676 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq695 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq568
       have i₂ := eq683 x y
       grind)
    | exact superpose eq683 eq568
    | exact resolve eq568 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq683
  have eq696 : False := by grind
  exact eq696

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    grind
  have eq82 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq101 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X0) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 (M.op X2 (M.op x X0)) (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2 x
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq152 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X3 X2 X4 X0
       have i₂ := eq101 X2 X0 X3 X1
       grind)
    | (have i₁ := eq20 X3 X2 X4 X0
       have i₂ := eq101 X2 X0 X1 X3
       grind)
    | exact superpose eq101 eq20
    | exact resolve eq20 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq101
  have eq321 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq348 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq321 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq349 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq357 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq349 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq349
    | (have j0 := eq349 X0 X1
       grind)
    | exact resolve eq349 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq358 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq357 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq1196 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq358 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq358
    | exact resolve eq358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1210 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq358 x y
       grind)
    | exact superpose eq358 eq16
    | (have j1 := eq358 x y
       grind)
    | exact resolve eq16 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq1239 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1196 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1196
    | (have j0 := eq1196 X0 X1
       grind)
    | exact resolve eq1196 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1196
  have eq1240 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1239 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1239
    | exact resolve eq1239 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1301 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1240 (τ X1) X0
       grind)
    | exact superpose eq1240 eq18
    | (have j1 := eq1240 (τ X1) X0
       grind)
    | exact resolve eq18 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1240
  have eq1488 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1301 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1301
    | exact resolve eq1301 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1534 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1488 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1488
    | (have j0 := eq1488 X0 X1
       grind)
    | exact resolve eq1488 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1840 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X1 (M.op X2 (M.op X3 X0)))) X0) = (M.op X0 (M.op X0 (M.op X1 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110 (M.op X2 (M.op X3 X0)) X0 X2
       have i₂ := eq9 X0 (M.op X2 (M.op X2 (M.op X3 X0))) X2 X3
       grind)
    | exact superpose eq9 eq110
    | exact resolve eq110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1860 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (k (M.op X0 (M.op X1 (M.op X2 (M.op X3 X0)))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1840 X0 X1 X2 X3
       have i₂ := eq152 X1 X2 (M.op X3 X0) X0 X0
       grind)
    | exact superpose eq152 eq1840
    | exact resolve eq1840 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq1876 : ∀ X0 X3 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq1860 X0 x x X3
       have i₂ := eq152 x X3 X0 X0 x
       grind)
    | exact superpose eq152 eq1860
    | exact resolve eq1860 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1860
  have eq2644 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1210
       have i₂ := eq1534 y x
       grind)
    | exact superpose eq1534 eq1210
    | (have j1 := eq1534 (σ y) (σ x)
       grind)
    | (have r₁ := eq1210
       have r₂ := eq1534 y x
       grind)
    | exact resolve eq1210 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2645 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2644
  have eq2673 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1876 x x
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq1876
    | exact resolve eq1876 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq2797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1210
       have i₂ := eq2673
       grind)
    | exact superpose eq2673 eq1210
    | exact resolve eq1210 eq2673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210 eq2673
  have eq2798 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2797
  have eq2799 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2798
  have eq2889 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1876 (σ x) (σ x)
       have i₂ := eq2799
       grind)
    | exact superpose eq2799 eq1876
    | exact resolve eq1876 eq2799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799
  have eq2894 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq2889
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2889
    | exact resolve eq2889 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2889
  have eq3054 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2894
       grind)
    | exact superpose eq2894 eq16
    | exact resolve eq16 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894
  have eq3096 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3054
       have i₂ := eq1534 y x
       grind)
    | exact superpose eq1534 eq3054
    | (have j1 := eq1534 y x
       grind)
    | (have r₁ := eq3054
       have r₂ := eq1534 y x
       grind)
    | exact resolve eq3054 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq3097 : y = (M.op x x) := by grind
  clear eq3096
  have eq3209 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1876 x x
       have i₂ := eq3097
       grind)
    | exact superpose eq3097 eq1876
    | exact resolve eq1876 eq3097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876 eq3097
  have eq3357 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq3054
       have i₂ := eq3209
       grind)
    | exact superpose eq3209 eq3054
    | exact resolve eq3054 eq3209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3054 eq3209
  have eq3360 : False := by grind
  exact eq3360

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyy_x_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq174 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 X1 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 (M.op X1 (M.op X2 X0)) X3 X4 (M.op X0 x)
       have i₂ := eq16 X0 x X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq16 X0 x x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, X0 ≠ X2 ∨ (k X2 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X2 (M.op x X2))
       have i₂ := eq16 X2 (M.op x X2) X2 x
       grind)
    | exact superpose eq16 eq13
    | (have r₁ := eq13 X2 (M.op X2 (M.op x X2))
       have r₂ := eq16 X2 (M.op x X2) X2 x
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X1 X1) X1) (M.op X2 (M.op x (M.op X1 X1)))) X1
       have r₂ := eq16 (M.op X1 X1) X1 X2 x
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X2 X3 : G, (M.op x y) = (M.op x (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X2 X3
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, y ≠ X0 ∨ y = (k X0 (M.op y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq177 eq13
    | (have r₁ := eq13 y (M.op y (M.op x y))
       have r₂ := eq177 (M.op x y) y
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ y) = (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq178 eq13
    | (have r₁ := eq13 (σ y) (M.op (σ y) (M.op (σ x) (σ y)))
       have r₂ := eq178 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq182 (M.op x (M.op x x))
       have i₂ := eq16 x (M.op x x) x x
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : (σ y) = (k (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq178 eq182
    | exact resolve eq182 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq182 x
       grind)
    | exact superpose eq182 eq39
    | exact resolve eq39 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op x (M.op X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq35 (M.op x (M.op X0 x))
       have i₂ := eq203 x X0
       grind)
    | exact superpose eq203 eq35
    | exact resolve eq35 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq238 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op x (M.op X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq233 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq233
    | (have j0 := eq233 X0
       grind)
    | exact resolve eq233 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq239 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (σ x) (M.op X0 (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op sF2 (M.op x sF2))
       have i₂ := eq203 sF2 x
       grind)
    | exact superpose eq203 eq90
    | exact resolve eq90 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq203
  have eq250 : ∀ X0 : G, x = (k x (τ (M.op (σ x) (M.op X0 (σ x))))) := by
    intro X0
    first
    | exact superpose eq29 eq239
    | exact resolve eq239 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq283 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq141
    | exact resolve eq141 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X0 X3) (M.op X0 X3)) ∨ (M.op X1 (M.op X2 X0)) = X0 ∨ (k (M.op X1 (M.op X2 X0)) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (M.op X2 (M.op X3 X0)) (M.op X0 X1)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 (M.op X1 (M.op X2 X0)) (M.op X0 X3)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq590 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq182 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq182
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (k X0 X1))) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X2 X3 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq593 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq987 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq16 X0 x X1 X2
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq177 eq176
    | exact resolve eq176 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq178 eq176
    | exact resolve eq176 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X2 (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 y X2 X0
       have i₂ := eq988 X0 X1
       grind)
    | (have i₁ := eq176 x y x X0
       have i₂ := eq988 X0 X1
       grind)
    | exact superpose eq988 eq176
    | exact resolve eq176 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X2 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq989 eq176
    | exact resolve eq176 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 X3 X2 X4 X0
       have i₂ := eq987 X2 X0 X3 X1
       grind)
    | (have i₁ := eq176 X3 X2 X4 X0
       have i₂ := eq987 X2 X0 X1 X3
       grind)
    | exact superpose eq987 eq176
    | exact resolve eq176 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1570 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq587
       grind)
    | exact superpose eq587 eq39
    | exact resolve eq39 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1571 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1570
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1570
    | exact resolve eq1570 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq1573 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1571
    | exact resolve eq1571 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571
  have eq1739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1573 eq590
    | exact resolve eq590 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq1748 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1739
       have r₂ := eq27
       grind)
    | exact resolve eq1739 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq1753 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1748 eq283
    | exact resolve eq283 eq1748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq1777 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq1753
    | exact resolve eq1753 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1779 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1777
       have r₂ := eq576
       grind)
    | exact resolve eq1777 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq1777
  have eq1781 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq587
       have i₂ := eq1779
       grind)
    | exact superpose eq1779 eq587
    | exact resolve eq587 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1783 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1779
       grind)
    | exact superpose eq1779 eq39
    | exact resolve eq39 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1787 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1781
  have eq1790 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1783
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1783
    | exact resolve eq1783 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq1794 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq206
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq206
    | exact resolve eq206 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq1797 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq238 x
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq238
    | exact resolve eq238 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq1798 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq174 X0 x
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq174
    | exact resolve eq174 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1799 : y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq182
    | exact resolve eq182 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1800 : ∀ X0 : G, y ≠ X0 ∨ y = (k X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq1787
       grind)
    | exact resolve eq13 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1804 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1 x
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq16
    | exact resolve eq16 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1805 : ∀ X0 X1 : G, y = (M.op x (M.op X0 (M.op X1 y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x x x x
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq176
    | exact resolve eq176 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1813 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1805 X0 x
       have i₂ := eq988 X0 x
       grind)
    | (have i₁ := eq1805 X0 x
       have i₂ := eq988 X0 x
       grind)
    | exact superpose eq988 eq1805
    | (have j0 := eq1805 X0 x
       grind)
    | exact resolve eq1805 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq1814 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1804 X0 x
       have i₂ := eq988 (M.op x X0) x
       grind)
    | (have i₁ := eq1804 X0 x
       have i₂ := eq988 (M.op x X0) x
       grind)
    | exact superpose eq988 eq1804
    | (have j0 := eq1804 X0 x
       grind)
    | exact resolve eq1804 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804
  have eq1816 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1798 x
       have i₂ := eq988 sF0 x
       grind)
    | (have i₁ := eq1798 x
       have i₂ := eq988 sF0 x
       grind)
    | exact superpose eq988 eq1798
    | (have j0 := eq1798 x
       grind)
    | exact resolve eq1798 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq1817 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1797
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1797
    | exact resolve eq1797 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq1818 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1794
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1794
    | exact resolve eq1794 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq1820 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1817
    | exact resolve eq1817 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq1867 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1818 eq590
    | exact resolve eq590 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq1873 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1867
  have eq1912 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1820 eq634
    | (have j0 := eq634 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq634 (σ (M.op x y)) (σ x)
       have r₂ := eq1820
       grind)
    | exact resolve eq634 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq1913 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1912
  have eq1923 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1873 eq175
    | exact resolve eq175 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1941 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq989 eq1923
    | (have j0 := eq1923 (σ x)
       grind)
    | exact resolve eq1923 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq1955 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1941 eq188
    | exact resolve eq188 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941
  have eq2007 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1790 eq590
    | exact resolve eq590 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq2013 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2007
  have eq2022 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1873 eq2013
    | exact resolve eq2013 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2082 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) x) ∨ y = (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1813 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq2096 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) x) ∨ (M.op X0 (M.op x y)) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2082 X0
       have j1 := eq1800 (M.op X0 (M.op x y))
       grind)
    | (have r₁ := eq2082 X0
       have r₂ := eq1800 (k (M.op X0 (M.op x y)) x)
       grind)
    | (have r₁ := eq2082 X0
       have r₂ := eq1800 (M.op X0 (M.op x y))
       grind)
    | (have r₁ := eq2082 X0
       have r₂ := eq1800 (M.op x y)
       grind)
    | exact resolve eq2082 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082
  have eq2099 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) x) ∨ y = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1787 eq2096
    | (have j0 := eq2096 X0
       grind)
    | exact resolve eq2096 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787 eq2096
  have eq2101 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2099 X0
       have j1 := eq1800 (M.op X0 (M.op x y))
       grind)
    | (have r₁ := eq2099 X0
       have r₂ := eq1800 (k (M.op X0 (M.op x y)) x)
       grind)
    | (have r₁ := eq2099 X0
       have r₂ := eq1800 (M.op X0 (M.op x y))
       grind)
    | (have r₁ := eq2099 X0
       have r₂ := eq1800 (M.op x y)
       grind)
    | exact resolve eq2099 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800 eq2099
  have eq2151 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2022 eq283
    | exact resolve eq283 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2155 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2022 eq175
    | exact resolve eq175 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2157 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ y) = (k X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2022 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2022
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq2022
       grind)
    | exact resolve eq13 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2162 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op X1 (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq2022 eq176
    | exact resolve eq176 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2170 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq989 eq2162
    | (have j0 := eq2162 X0 (σ x)
       grind)
    | exact resolve eq2162 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq2173 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq989 eq2155
    | (have j0 := eq2155 (σ x)
       grind)
    | exact resolve eq2155 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq2175 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq31 eq2151
    | exact resolve eq2151 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq2224 : y = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1816 eq2101
    | exact resolve eq2101 eq1816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816 eq2101
  have eq2227 : y = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2224
  have eq2450 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ X3 ∨ (M.op X0 (M.op X1 X2)) = (k X3 (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X0)) X0)
       have i₂ := eq179 X0 X1 X2 X0 (M.op X1 (M.op X2 X0))
       grind)
    | exact superpose eq179 eq13
    | (have r₁ := eq13 (M.op (M.op (M.op (M.op X2 X0) (M.op X2 X0)) X3) (M.op x X0)) (M.op X2 X0)
       have r₂ := eq179 X0 (M.op X2 X0) X2 X3 x
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)
       have r₂ := eq179 X0 X1 X2 X0 (M.op X1 (M.op X2 X0))
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2554 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq174 X0 x
       have i₂ := eq2175
       grind)
    | exact superpose eq2175 eq174
    | exact resolve eq174 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2556 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq2175
       grind)
    | exact superpose eq2175 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq2175
       grind)
    | exact resolve eq13 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2567 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0 X1
    first
    | (have i₁ := eq987 x X0 x X1
       have i₂ := eq2175
       grind)
    | exact superpose eq2175 eq987
    | exact resolve eq987 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3831 : ∀ X0 : G, (σ y) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2170 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170
  have eq3858 : ∀ X0 : G, (σ y) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq3831 X0
       have j1 := eq2157 (M.op X0 (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq3831 X0
       have r₂ := eq2157 (k (M.op X0 (M.op (σ x) (σ y))) (σ x))
       grind)
    | (have r₁ := eq3831 X0
       have r₂ := eq2157 (M.op X0 (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq3831 X0
       have r₂ := eq2157 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq3831 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831
  have eq3861 : ∀ X0 : G, (σ y) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2022 eq3858
    | (have j0 := eq3858 X0
       grind)
    | exact resolve eq3858 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022 eq3858
  have eq3863 : ∀ X0 : G, (σ y) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq3861 X0
       have j1 := eq2157 (M.op X0 (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq3861 X0
       have r₂ := eq2157 (k (M.op X0 (M.op (σ x) (σ y))) (σ x))
       grind)
    | (have r₁ := eq3861 X0
       have r₂ := eq2157 (M.op X0 (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq3861 X0
       have r₂ := eq2157 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq3861 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157 eq3861
  have eq4110 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0
    first
    | exact superpose eq2554 eq1016
    | exact resolve eq1016 eq2554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4146 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0
    first
    | exact superpose eq1799 eq4110
    | exact resolve eq4110 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4110
  have eq4229 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2173 eq3863
    | exact resolve eq3863 eq2173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173 eq3863
  have eq4237 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq4229
  have eq4247 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq4237 eq97
    | exact resolve eq97 eq4237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4237
  have eq4262 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq31 eq4247
    | exact resolve eq4247 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4247
  have eq4272 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq174 X0 x
       have i₂ := eq4262
       grind)
    | exact superpose eq4262 eq174
    | exact resolve eq174 eq4262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4262
  have eq4533 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op X2 x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq987 x X1 X0 X2
       have i₂ := eq4146 X0
       grind)
    | exact superpose eq4146 eq987
    | exact resolve eq987 eq4146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4146
  have eq4585 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X1 (M.op X0 (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0 X1
    first
    | exact superpose eq2567 eq4533
    | exact resolve eq4533 eq2567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567 eq4533
  have eq4859 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq4272 eq1016
    | exact resolve eq1016 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4900 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq2227 eq4859
    | exact resolve eq4859 eq2227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq5160 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op X0 (M.op X1 (M.op x y))) ∨ (M.op x y) = (k (M.op X0 (M.op X1 (M.op x y))) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0 X1
    first
    | exact superpose eq2554 eq582
    | (have j0 := eq582 (M.op x y) X0 X1 x
       grind)
    | exact resolve eq582 eq2554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq5305 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = X2 ∨ (M.op X0 (M.op X1 X2)) = X2 ∨ (k (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X3 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X3 X2) X2 X3
       have i₂ := eq582 X2 X0 X1 (M.op X3 X2)
       grind)
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq582 (M.op X3 X0) (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq582 eq16
    | (have j1 := eq582 X2 X0 X1 (M.op X3 X2)
       grind)
    | exact resolve eq16 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5309 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 X4)))) ∨ (M.op X2 (M.op X3 X4)) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 X4)))) ∨ (M.op X2 (M.op X3 X4)) = (k (M.op X0 (M.op X1 (M.op X2 (M.op X3 X4)))) (M.op (M.op X2 (M.op X3 X4)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq179 X4 X2 X3 X4 (M.op X2 (M.op X3 X4))
       have i₂ := eq582 (M.op X2 (M.op X3 X4)) X0 X1 X4
       grind)
    | (have i₁ := eq179 X0 X1 X2 X3 X2
       have i₂ := eq582 X0 (M.op (M.op X1 (M.op X2 X0)) X3) X2 X3
       grind)
    | exact superpose eq582 eq179
    | (have j1 := eq582 (M.op X2 (M.op X3 X4)) X0 X1 X4
       grind)
    | exact resolve eq179 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq5310 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 y)) ∨ y = (M.op X0 (M.op X1 y)) ∨ y = (k (M.op X0 (M.op X1 y)) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 x
       have i₂ := eq582 sF0 (M.op y X0) x x
       grind)
    | (have i₁ := eq177 sF0 y
       have i₂ := eq582 y X1 x sF0
       grind)
    | exact superpose eq582 eq177
    | (have j1 := eq582 y X0 X1 (M.op x y)
       grind)
    | exact resolve eq177 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5312 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (σ y))) ∨ (σ y) = (M.op X0 (M.op X1 (σ y))) ∨ (σ y) = (k (M.op X0 (M.op X1 (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 x
       have i₂ := eq582 sF4 (M.op sF3 X0) x x
       grind)
    | (have i₁ := eq178 sF4 sF3
       have i₂ := eq582 sF3 X1 x sF4
       grind)
    | exact superpose eq582 eq178
    | (have j1 := eq582 (σ y) X0 X1 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq178 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq5367 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (σ y))) ∨ (σ y) = (k (M.op X0 (M.op X1 (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have j0 := eq5312 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5312
  have eq5369 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 y)) ∨ y = (k (M.op X0 (M.op X1 y)) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | (have j0 := eq5310 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5310
  have eq5370 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 X4)))) ∨ (M.op X2 (M.op X3 X4)) = (k (M.op X0 (M.op X1 (M.op X2 (M.op X3 X4)))) (M.op (M.op X2 (M.op X3 X4)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq5309 X0 X1 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309
  have eq5374 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = X2 ∨ (k (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X3 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq5305 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5305
  have eq5397 : ∀ X0 X1 : G, (σ y) = (k (M.op X0 (M.op X1 (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have j0 := eq5367 X0 X1
       have j1 := eq197 (M.op X0 (M.op X1 (σ y)))
       grind)
    | (have r₁ := eq5367 X0 X1
       have r₂ := eq197 (M.op X0 (M.op X1 (σ y)))
       grind)
    | (have r₁ := eq5367 X0 X1
       have r₂ := eq197 (k (M.op X0 (M.op X1 (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq5367 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq5367
  have eq5399 : ∀ X0 X1 : G, y = (k (M.op X0 (M.op X1 y)) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | (have j0 := eq5369 X0 X1
       have j1 := eq190 (M.op X0 (M.op X1 y))
       grind)
    | (have r₁ := eq5369 X0 X1
       have r₂ := eq190 (M.op X0 (M.op X1 y))
       grind)
    | (have r₁ := eq5369 X0 X1
       have r₂ := eq190 (k (M.op X0 (M.op X1 y)) (M.op y (M.op x y)))
       grind)
    | exact resolve eq5369 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq5369
  have eq5400 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (k (M.op X0 (M.op X1 (M.op X2 (M.op X3 X4)))) (M.op (M.op X2 (M.op X3 X4)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq5370 X0 X1 X2 X3 X4
       have j1 := eq2450 X2 X3 X4 (M.op X0 (M.op X1 (M.op X2 (M.op X3 X4))))
       grind)
    | (have r₁ := eq5370 X0 X1 X0 X1 X2
       have r₂ := eq2450 X0 X1 X2 (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2))))
       grind)
    | (have r₁ := eq5370 X0 X1 X2 X3 X4
       have r₂ := eq2450 X0 X1 (M.op X2 (M.op X3 X4)) (M.op X2 (M.op X3 X4))
       grind)
    | (have r₁ := eq5370 X0 X1 X0 X1 X2
       have r₂ := eq2450 X0 X1 X2 (k (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) (M.op (M.op X0 (M.op X1 X2)) X2))
       grind)
    | exact resolve eq5370 eq2450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450 eq5370
  have eq5404 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X3 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq5374 X0 X1 X2 X3
       have j1 := eq181 X2 X3 (M.op X0 (M.op X1 X2))
       grind)
    | (have r₁ := eq5374 X0 X1 X2 X3
       have r₂ := eq181 (M.op X0 (M.op X1 X2)) X1 X2
       grind)
    | (have r₁ := eq5374 X0 X1 X0 X3
       have r₂ := eq181 X0 X1 (M.op X0 (M.op X1 X0))
       grind)
    | (have r₁ := eq5374 X0 X1 X2 X3
       have r₂ := eq181 (k (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X3 X2))) X1 X2
       grind)
    | exact resolve eq5374 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq5374
  have eq5463 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (M.op x x) ∨ (M.op x y) = (k (M.op X0 (M.op X1 (M.op x y))) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0 X1
    first
    | (have j0 := eq5160 X0 X1
       have j1 := eq2556 (M.op X0 (M.op X1 (M.op x y)))
       grind)
    | (have r₁ := eq5160 X0 X1
       have r₂ := eq2556 (M.op X0 (M.op X1 (M.op x y)))
       grind)
    | (have r₁ := eq5160 X0 X1
       have r₂ := eq2556 (k (M.op X0 (M.op X1 (M.op x y))) x)
       grind)
    | exact resolve eq5160 eq2556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5160
  have eq5480 : ∀ X0 : G, (σ y) = (k (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq989 eq5397
    | (have j0 := eq5397 X0 (σ x)
       grind)
    | exact resolve eq5397 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5397
  have eq5482 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq5399 X0 x
       have i₂ := eq988 X0 x
       grind)
    | (have i₁ := eq5399 X0 x
       have i₂ := eq988 X0 x
       grind)
    | exact superpose eq988 eq5399
    | (have j0 := eq5399 X0 x
       grind)
    | exact resolve eq5399 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5399
  have eq5483 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (k (M.op X0 X4) (M.op (M.op X2 (M.op X3 X4)) X4)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq5400 X0 x X2 X3 X4
       have i₂ := eq1169 X2 X3 X4 X0 x
       grind)
    | exact superpose eq1169 eq5400
    | exact resolve eq5400 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq5400
  have eq5533 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 (M.op x y))) ∨ (M.op x y) = (k (M.op X0 (M.op X1 (M.op x y))) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0 X1
    first
    | exact superpose eq1779 eq5463
    | (have j0 := eq5463 X0 X1
       grind)
    | exact resolve eq5463 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779 eq5463
  have eq5560 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 (M.op x y))) ∨ (M.op x y) = (k (M.op X0 (M.op X1 (M.op x y))) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0 X1
    first
    | exact superpose eq1799 eq5533
    | (have j0 := eq5533 X0 X1
       grind)
    | exact resolve eq5533 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799 eq5533
  have eq5579 : ∀ X0 X1 : G, (M.op x y) = (k (M.op X0 (M.op X1 (M.op x y))) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0 X1
    first
    | (have j0 := eq5560 X0 X1
       have j1 := eq2556 (M.op X0 (M.op X1 (M.op x y)))
       grind)
    | (have r₁ := eq5560 X0 X1
       have r₂ := eq2556 (M.op X0 (M.op X1 (M.op x y)))
       grind)
    | (have r₁ := eq5560 X0 X1
       have r₂ := eq2556 (k (M.op X0 (M.op X1 (M.op x y))) x)
       grind)
    | exact resolve eq5560 eq2556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556 eq5560
  have eq5580 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    intro X0
    first
    | exact superpose eq4585 eq5579
    | exact resolve eq5579 eq4585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4585 eq5579
  have eq6132 : ∀ X0 X1 X2 : G, x = (M.op (M.op x X1) (M.op X2 (M.op X0 (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 x X1 X2 X0
       have i₂ := eq4900 X0
       grind)
    | exact superpose eq4900 eq16
    | exact resolve eq16 eq4900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4900
  have eq6227 : ∀ X1 : G, x = (M.op (M.op x X1) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    intro X1
    first
    | exact superpose eq1016 eq6132
    | exact resolve eq6132 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016 eq6132
  have eq6235 : ∀ X1 : G, x = (M.op (M.op x X1) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    intro X1
    first
    | exact superpose eq2227 eq6227
    | exact resolve eq6227 eq2227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6227
  have eq6239 : ∀ X1 : G, x = (M.op (M.op x X1) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    intro X1
    first
    | exact superpose eq1814 eq6235
    | (have j0 := eq6235 X1
       have j1 := eq1814 X1
       grind)
    | exact resolve eq6235 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814 eq6235
  have eq6535 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq6239 eq177
    | exact resolve eq177 eq6239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq6536 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq6239 eq185
    | exact resolve eq185 eq6239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6548 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq6239 eq5580
    | exact resolve eq5580 eq6239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5580 eq6239
  have eq6567 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by grind
  clear eq6548
  have eq6602 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq6567
       grind)
    | exact superpose eq6567 eq39
    | exact resolve eq39 eq6567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6567
  have eq6617 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq6602
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6602
    | exact resolve eq6602 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6602
  have eq6619 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq20 eq6617
    | exact resolve eq6617 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6617
  have eq6900 : ∀ X0 X2 : G, x = (k (M.op X0 y) (M.op x (M.op X2 x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    intro X0 X2
    first
    | (have i₁ := eq5404 X0 (M.op y x) x X2
       have i₂ := eq6535 x
       grind)
    | exact superpose eq6535 eq5404
    | exact resolve eq5404 eq6535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq6988 : ∀ X1 : G, (M.op x y) = (k x (M.op (M.op x y) (M.op X1 (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    intro X1
    first
    | exact superpose eq4272 eq5404
    | exact resolve eq5404 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7202 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq4272 eq6988
    | exact resolve eq6988 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4272 eq6988
  have eq7265 : ∀ X0 : G, x = (k (M.op X0 y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq6536 eq6900
    | exact resolve eq6900 eq6536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536 eq6900
  have eq7448 : y ≠ (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by grind
  clear eq7202
  have eq7454 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7448
       have r₂ := eq2227
       grind)
    | exact resolve eq7448 eq2227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227 eq7448
  have eq7468 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq7454
       grind)
    | exact superpose eq7454 eq39
    | exact resolve eq39 eq7454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7472 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq597 x x X0 X1
       have i₂ := eq7454
       grind)
    | exact superpose eq7454 eq597
    | (have j0 := eq597 x x x x
       grind)
    | exact resolve eq597 eq7454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7473 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq634 x x
       have i₂ := eq7454
       grind)
    | exact superpose eq7454 eq634
    | (have j0 := eq634 x x
       grind)
    | exact resolve eq634 eq7454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7474 : x ≠ y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7473
  have eq7475 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq7472 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7472
  have eq7484 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7475 X0 x
       have i₂ := eq988 (M.op x X0) x
       grind)
    | (have i₁ := eq7475 X0 x
       have i₂ := eq988 (M.op x X0) x
       grind)
    | exact superpose eq988 eq7475
    | (have j0 := eq7475 X0 x
       grind)
    | exact resolve eq7475 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7475
  have eq7485 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7468
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7468
    | exact resolve eq7468 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7468
  have eq7487 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7485
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7485
    | exact resolve eq7485 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7485
  have eq7495 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7487 eq6619
    | exact resolve eq6619 eq7487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6619
  have eq7502 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7487 eq634
    | (have j0 := eq634 (σ x) (σ x)
       grind)
    | exact resolve eq634 eq7487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7503 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7502
  have eq7506 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq7495
  have eq7590 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq7506
       grind)
    | exact superpose eq7506 eq39
    | exact resolve eq39 eq7506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7506
  have eq7600 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq7590
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7590
    | exact resolve eq7590 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7590
  have eq7627 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7600 eq590
    | exact resolve eq590 eq7600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7600
  have eq7636 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq7627
  have eq7664 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op X1 (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq7636 eq16
    | exact resolve eq16 eq7636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7679 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq7636 eq987
    | exact resolve eq987 eq7636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7698 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq7679 eq7664
    | exact resolve eq7664 eq7679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7664 eq7679
  have eq7704 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq989 eq7698
    | (have j0 := eq7698 (σ x)
       grind)
    | exact resolve eq7698 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7698
  have eq9192 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7484 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7484
    | (have j0 := eq7484 y
       grind)
    | exact resolve eq7484 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7484
  have eq9328 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9192 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq9192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9192
  have eq9348 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9328
  have eq9432 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7265 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7265
    | (have j0 := eq7265 x
       grind)
    | exact resolve eq7265 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7265
  have eq9457 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq634 x x
       have i₂ := eq9432
       grind)
    | exact superpose eq9432 eq634
    | (have j0 := eq634 x x
       grind)
    | exact resolve eq634 eq9432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9432
  have eq9458 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq9457
  have eq9467 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq9458
       have r₂ := eq9348
       grind)
    | exact resolve eq9458 eq9348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9348 eq9458
  have eq9478 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq9467 eq41
    | exact resolve eq41 eq9467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq9467
  have eq9487 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq9478
    | exact resolve eq9478 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9478
  have eq9489 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9487
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9487
    | exact resolve eq9487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9487
  have eq11451 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1913 eq1955
    | exact resolve eq1955 eq1913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1913
  have eq11487 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq11451
  have eq11503 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1873 eq11487
    | exact resolve eq11487 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873 eq11487
  have eq11504 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11503
  have eq11518 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq11504 eq16
    | exact resolve eq16 eq11504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11533 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq11504 eq987
    | exact resolve eq987 eq11504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11504
  have eq11542 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f11542_14 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f11542_15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ (M.op x y)))) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f11542_24 : (σ (M.op x y)) ≠ (M.op (σ x) (M.op X0 (σ x))) := by grind
    have f11542_25 : y ≠ (M.op x y) := by grind
    have f11542_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f11542_28 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ (M.op x y)))) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f11542_15 X0 X1
         grind)
      | (have r₁ := f11542_15 X0 X1
         have r₂ := f11542_25
         grind)
      | exact resolve f11542_15 f11542_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11542_29 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f11542_14 X0 X1
         grind)
      | (have r₁ := f11542_14 X0 X1
         have r₂ := f11542_25
         grind)
      | exact resolve f11542_14 f11542_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11542_30 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ (M.op x y)))) = (M.op X0 (σ x)) := by
      intro X0 X1
      first
      | (have j0 := f11542_28 X0 X1
         grind)
      | (have r₁ := f11542_28 X0 X1
         have r₂ := f11542_26
         grind)
      | exact resolve f11542_28 f11542_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11542_31 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) := by
      intro X0 X1
      first
      | (have j0 := f11542_29 X0 X1
         grind)
      | (have r₁ := f11542_29 X0 X1
         have r₂ := f11542_26
         grind)
      | exact resolve f11542_29 f11542_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11542_32 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) := by
      intro X0
      first
      | (have i₁ := f11542_31 X0 x
         have i₂ := f11542_30 X0 x
         grind)
      | exact superpose f11542_30 f11542_31
      | exact resolve f11542_31 f11542_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11542_47 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
      first
      | (have i₁ := f11542_24
         have i₂ := f11542_32 X0
         grind)
      | exact superpose f11542_32 f11542_24
      | (have r₁ := f11542_24
         have r₂ := f11542_32 X0
         grind)
      | exact resolve f11542_24 f11542_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11542_53 : False := by grind
    exact f11542_53
  clear eq11518 eq11533
  have eq11856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11542 eq1955
    | exact resolve eq1955 eq11542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955 eq11542
  have eq11906 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11856
  have eq11944 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11906
       have r₂ := eq27
       grind)
    | exact resolve eq11906 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11906
  have eq11976 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11944 eq27
    | exact resolve eq27 eq11944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11984 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11944 eq579
    | (have r₁ := eq579
       have r₂ := eq11944
       grind)
    | exact resolve eq579 eq11944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq11988 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11984
  have eq12358 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11988 eq141
    | exact resolve eq141 eq11988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11988
  have eq12372 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq12358
    | exact resolve eq12358 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12358
  have eq12380 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12372 eq283
    | exact resolve eq283 eq12372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq12372
  have eq12439 : y = (k y x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq12380
    | exact resolve eq12380 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12380
  have eq12440 : y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq12439
  have eq12450 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq587
       have i₂ := eq12440
       grind)
    | exact superpose eq12440 eq587
    | exact resolve eq587 eq12440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq12452 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq12440
       grind)
    | exact superpose eq12440 eq39
    | exact resolve eq39 eq12440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12440
  have eq12457 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq12450
  have eq12464 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12452
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12452
    | exact resolve eq12452 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12452
  have eq12480 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq174 X0 x
       have i₂ := eq12457
       grind)
    | exact superpose eq12457 eq174
    | exact resolve eq174 eq12457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq12498 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x x X0 X1
       have i₂ := eq12457
       grind)
    | exact superpose eq12457 eq16
    | exact resolve eq16 eq12457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12503 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq180 x x x
       have i₂ := eq12457
       grind)
    | exact superpose eq12457 eq180
    | exact resolve eq180 eq12457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq12513 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq987 x X0 x X1
       have i₂ := eq12457
       grind)
    | exact superpose eq12457 eq987
    | exact resolve eq987 eq12457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12534 : ∀ X0 : G, x = (M.op y (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12513 eq12498
    | exact resolve eq12498 eq12513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12498
  have eq12536 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12480 x
       have i₂ := eq988 sF0 x
       grind)
    | (have i₁ := eq12480 x
       have i₂ := eq988 sF0 x
       grind)
    | exact superpose eq988 eq12480
    | (have j0 := eq12480 x
       grind)
    | exact resolve eq12480 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12480
  have eq12540 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12534 x
       have i₂ := eq988 y x
       grind)
    | (have i₁ := eq12534 x
       have i₂ := eq988 y x
       grind)
    | exact superpose eq988 eq12534
    | (have j0 := eq12534 x
       grind)
    | exact resolve eq12534 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12534
  have eq12591 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12536 eq185
    | exact resolve eq185 eq12536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq12603 : y = (k x (M.op y (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12536 eq5482
    | exact resolve eq5482 eq12536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5482
  have eq12628 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12536 eq987
    | exact resolve eq987 eq12536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12629 : ∀ X0 X1 : G, (M.op x y) = (k (M.op X0 x) (M.op (M.op x y) (M.op X1 (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12536 eq5404
    | exact resolve eq5404 eq12536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12640 : y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12540 eq12603
    | exact resolve eq12603 eq12540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12540 eq12603
  have eq12736 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq12640
       grind)
    | exact superpose eq12640 eq39
    | exact resolve eq39 eq12640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12756 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12736
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12736
    | exact resolve eq12736 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12736
  have eq12759 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12756
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12756
    | exact resolve eq12756 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12756
  have eq12774 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12759 eq597
    | (have j0 := eq597 (σ x) (σ x) x x
       grind)
    | exact resolve eq597 eq12759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq12775 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12759 eq634
    | (have j0 := eq634 (σ x) (σ x)
       grind)
    | exact resolve eq634 eq12759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12776 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12775
  have eq12777 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq12774 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12774
  have eq12779 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq989 eq12777
    | (have j0 := eq12777 X0 (σ x)
       grind)
    | exact resolve eq12777 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12777
  have eq12786 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11944 eq12779
    | exact resolve eq12779 eq11944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12779
  have eq14382 : ∀ X0 : G, (M.op x y) = (k (M.op X0 x) (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12628 eq12629
    | exact resolve eq12629 eq12628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12628 eq12629
  have eq14396 : ∀ X0 : G, (M.op x y) = (k (M.op X0 x) (M.op (M.op x y) x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14382 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14382
  have eq14433 : (M.op x y) = (k y (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14396 x
       have i₂ := eq12457
       grind)
    | exact superpose eq12457 eq14396
    | exact resolve eq14396 eq12457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14396
  have eq14447 : (M.op x y) = (k y (M.op (M.op x y) x)) ∨ y = (M.op x y) := by grind
  clear eq14433
  have eq14457 : (σ (M.op x y)) = (k (σ y) (σ (M.op (M.op x y) x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14447 eq36
    | exact resolve eq36 eq14447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq14447
  have eq14461 : (σ (M.op x y)) = (k (σ y) (σ (M.op (M.op x y) x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq14457
    | exact resolve eq14457 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14457
  have eq15461 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq188 eq12786
    | (have j0 := eq12786 (σ y)
       grind)
    | exact resolve eq12786 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq12786
  have eq15572 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11944 eq15461
    | exact resolve eq15461 eq11944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15461
  have eq15607 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15572 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq15572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15572
  have eq15627 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq15607
  have eq15650 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15627
       have r₂ := eq12776
       grind)
    | exact resolve eq15627 eq12776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12776 eq15627
  have eq15706 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15650 eq115
    | exact resolve eq115 eq15650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650
  have eq15721 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq15706
    | exact resolve eq15706 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15706
  have eq15906 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15721 eq182
    | exact resolve eq182 eq15721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15721
  have eq15955 : x = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12759 eq15906
    | exact resolve eq15906 eq12759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12759 eq15906
  have eq16354 : y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq639 x
       have i₂ := eq7454
       grind)
    | exact superpose eq7454 eq639
    | (have j0 := eq639 x
       grind)
    | exact resolve eq639 eq7454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7454
  have eq16379 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7487 eq639
    | (have j0 := eq639 (σ x)
       grind)
    | exact resolve eq639 eq7487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq16415 : y = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2175 eq16354
    | exact resolve eq16354 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175 eq16354
  have eq16423 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11944 eq16415
    | exact resolve eq16415 eq11944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16415
  have eq16586 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16379 eq141
    | exact resolve eq141 eq16379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16379
  have eq16596 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq16586
    | exact resolve eq16586 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16586
  have eq16600 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11944 eq16596
    | exact resolve eq16596 eq11944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16596
  have eq16710 : x = (k x (τ (M.op (σ x) (σ x)))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16600 eq250
    | exact resolve eq250 eq16600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq16782 : (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ x)))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16423 eq16710
    | exact resolve eq16710 eq16423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16423 eq16710
  have eq16790 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16600 eq16782
    | exact resolve eq16782 eq16600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16600 eq16782
  have eq16794 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq16790
    | exact resolve eq16790 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16790
  have eq16795 : (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16794
  have eq16797 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16795 eq39
    | exact resolve eq39 eq16795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq16795
  have eq16802 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16797
    | exact resolve eq16797 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16797
  have eq16810 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16802 eq634
    | (have j0 := eq634 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq634 (σ x) (σ (M.op x y))
       have r₂ := eq16802
       grind)
    | exact resolve eq634 eq16802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16802
  have eq16811 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16810
  have eq17089 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16811 eq7636
    | exact resolve eq7636 eq16811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7636
  have eq17126 : ∀ X0 X1 : G, (σ x) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq16811 eq16
    | exact resolve eq16 eq16811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17141 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq16811 eq987
    | exact resolve eq987 eq16811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16811
  have eq17164 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq17089
  have eq17178 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f17178_14 : ∀ X0 X1 : G, (σ x) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f17178_15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f17178_24 : (σ x) ≠ (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by grind
    have f17178_25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ (M.op x y))) := by grind
    have f17178_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f17178_28 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f17178_15 X0 X1
         grind)
      | (have r₁ := f17178_15 X0 X1
         have r₂ := f17178_25
         grind)
      | exact resolve f17178_15 f17178_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17178_29 : ∀ X0 X1 : G, (σ x) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f17178_14 X0 X1
         grind)
      | (have r₁ := f17178_14 X0 X1
         have r₂ := f17178_25
         grind)
      | exact resolve f17178_14 f17178_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17178_30 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ (M.op x y))) := by
      intro X0 X1
      first
      | (have j0 := f17178_28 X0 X1
         grind)
      | (have r₁ := f17178_28 X0 X1
         have r₂ := f17178_26
         grind)
      | exact resolve f17178_28 f17178_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17178_31 : ∀ X0 X1 : G, (σ x) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (σ x)))) := by
      intro X0 X1
      first
      | (have j0 := f17178_29 X0 X1
         grind)
      | (have r₁ := f17178_29 X0 X1
         have r₂ := f17178_26
         grind)
      | exact resolve f17178_29 f17178_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17178_78 : ∀ X0 : G, (σ x) ≠ (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (σ x)))) := by
      intro X0
      first
      | (have i₁ := f17178_24
         have i₂ := f17178_30 X0 X0
         grind)
      | exact superpose f17178_30 f17178_24
      | exact resolve f17178_24 f17178_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17178_79 : False := by
      first
      | (have r₁ := f17178_78 x
         have r₂ := f17178_31 X0 x
         grind)
      | exact resolve f17178_78 f17178_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f17178_79
  clear eq17126 eq17141
  have eq17185 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17164 eq17178
    | exact resolve eq17178 eq17164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17178
  have eq17189 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq989 eq17185
    | (have j0 := eq17185 (σ x)
       grind)
    | exact resolve eq17185 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17185
  have eq17192 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7704 eq17189
    | exact resolve eq17189 eq7704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7704 eq17189
  have eq17196 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17192
    | exact resolve eq17192 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17192
  have eq17197 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17196
  have eq17203 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17197 eq205
    | exact resolve eq205 eq17197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq17205 : ∀ X0 : G, (σ y) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17197 eq5480
    | exact resolve eq5480 eq17197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5480
  have eq17214 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17197 eq178
    | exact resolve eq178 eq17197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq17219 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq17197 eq1042
    | exact resolve eq1042 eq17197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq17246 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq17197 eq987
    | exact resolve eq987 eq17197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq17247 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq17197 eq5404
    | exact resolve eq5404 eq17197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5404 eq17197
  have eq17278 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17203 eq590
    | exact resolve eq590 eq17203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq17203
  have eq17286 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17278
  have eq17317 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17286 eq175
    | exact resolve eq175 eq17286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq17385 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq989 eq17317
    | (have j0 := eq17317 (σ x)
       grind)
    | exact resolve eq17317 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17317
  have eq17484 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op X0 (M.op (σ x) (σ y)))) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17205 eq141
    | exact resolve eq141 eq17205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq17205
  have eq17506 : ∀ X0 : G, y = (k (τ (M.op X0 (M.op (σ x) (σ y)))) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31 eq17484
    | exact resolve eq17484 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17484
  have eq17507 : ∀ X0 : G, (M.op x y) = (k (τ (M.op X0 (M.op (σ x) (σ y)))) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11944 eq17506
    | exact resolve eq17506 eq11944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11944 eq17506
  have eq18351 : (M.op x y) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17385 eq17507
    | exact resolve eq17507 eq17385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17507
  have eq18377 : (M.op x y) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18351
  have eq18399 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq18377
    | exact resolve eq18377 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18377
  have eq20567 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17246 eq17247
    | exact resolve eq17247 eq17246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17246 eq17247
  have eq20582 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq20567 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20567
  have eq23452 : ∀ X0 X1 : G, (M.op y (M.op X0 x)) = (k (M.op X1 x) y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq5483 X1 y X0 x
       have i₂ := eq12503 (M.op X0 x)
       grind)
    | exact superpose eq12503 eq5483
    | exact resolve eq5483 eq12503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12503
  have eq23473 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (σ x))) = (k (M.op X1 (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq17214 eq5483
    | exact resolve eq5483 eq17214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5483 eq17214
  have eq23559 : ∀ X1 : G, (M.op (σ y) (σ y)) = (k (M.op X1 (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq17219 eq23473
    | exact resolve eq23473 eq17219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17219 eq23473
  have eq23568 : ∀ X1 : G, (M.op y y) = (k (M.op X1 x) y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq12513 eq23452
    | exact resolve eq23452 eq12513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12513 eq23452
  have eq24445 : (k y y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23568 x
       have i₂ := eq12457
       grind)
    | exact superpose eq12457 eq23568
    | exact resolve eq23568 eq12457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23568
  have eq24455 : (k y y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq24445
  have eq24471 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq988 X0 y
       have i₂ := eq24455
       grind)
    | exact superpose eq24455 eq988
    | exact resolve eq988 eq24455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq24455
  have eq24784 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24471 X0
       have i₂ := eq15955
       grind)
    | exact superpose eq15955 eq24471
    | exact resolve eq24471 eq15955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955 eq24471
  have eq24883 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq24784 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24784
  have eq24990 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17286 eq23559
    | exact resolve eq23559 eq17286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17286 eq23559
  have eq24999 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24990
  have eq25046 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24999 eq989
    | exact resolve eq989 eq24999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq24999
  have eq26799 : (σ (M.op x y)) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14461
       have i₂ := eq24883 sF0
       grind)
    | exact superpose eq24883 eq14461
    | exact resolve eq14461 eq24883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14461 eq24883
  have eq26847 : (σ (M.op x y)) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq26799
  have eq26885 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12536 eq26847
    | exact resolve eq26847 eq12536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12536 eq26847
  have eq26924 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26885
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26885
    | exact resolve eq26885 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26885
  have eq26949 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12464 eq26924
    | exact resolve eq26924 eq12464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12464 eq26924
  have eq26960 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26949
       have r₂ := eq11976
       grind)
    | exact resolve eq26949 eq11976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11976 eq26949
  have eq26966 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26960 eq31
    | exact resolve eq31 eq26960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq26976 : (k y y) = (τ (k (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26960 eq115
    | exact resolve eq115 eq26960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq26960
  have eq27226 : (k x x) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq26976
    | exact resolve eq26976 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq26976
  have eq27236 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq26966
    | exact resolve eq26966 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq26966
  have eq27287 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12640 eq27226
    | exact resolve eq27226 eq12640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12640 eq27226
  have eq27304 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27236 eq27287
    | exact resolve eq27287 eq27236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27287
  have eq27321 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq27236
       grind)
    | exact superpose eq27236 eq24
    | exact resolve eq24 eq27236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27236
  have eq27368 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq27321
    | exact resolve eq27321 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27321
  have eq27545 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27368 eq9489
    | exact resolve eq9489 eq27368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9489 eq27368
  have eq27576 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq27545
       have r₂ := eq7474
       grind)
    | exact resolve eq27545 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7474 eq27545
  have eq28072 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq634 x x
       have i₂ := eq27304
       grind)
    | exact superpose eq27304 eq634
    | (have j0 := eq634 x x
       grind)
    | (have r₁ := eq634 x x
       have r₂ := eq27304
       grind)
    | exact resolve eq634 eq27304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq27304
  have eq28073 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq28072
  have eq28074 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq28073
  have eq28205 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12591 x
       have i₂ := eq28074
       grind)
    | exact superpose eq28074 eq12591
    | exact resolve eq12591 eq28074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12591 eq28074
  have eq28242 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq28205
  have eq28302 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12457
       have i₂ := eq28242
       grind)
    | exact superpose eq28242 eq12457
    | exact resolve eq12457 eq28242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12457 eq28242
  have eq28378 : y = (M.op x y) := by grind
  clear eq28302
  have eq28397 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq28378
       grind)
    | exact superpose eq28378 eq24
    | exact resolve eq24 eq28378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28378
  have eq28446 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28397 eq20
    | exact resolve eq20 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44351 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq27576 eq25046
    | exact resolve eq25046 eq27576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25046 eq27576
  have eq44393 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq44351 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44351
  have eq67397 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq44393 eq17385
    | exact resolve eq17385 eq44393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17385 eq44393
  have eq67419 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq67397
  have eq67689 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq67419 eq20582
    | exact resolve eq20582 eq67419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20582 eq67419
  have eq67750 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq67689
  have eq67808 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq7487 eq67750
    | exact resolve eq67750 eq7487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7487 eq67750
  have eq67809 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq67808
  have eq67899 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq67809
       grind)
    | exact superpose eq67809 eq182
    | exact resolve eq182 eq67809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq67809
  have eq67961 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18399 eq67899
    | exact resolve eq67899 eq18399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18399 eq67899
  have eq67989 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq67961 eq27
    | exact resolve eq27 eq67961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67961
  have eq68017 : x = (M.op x y) := by
    first
    | (have r₁ := eq67989
       have r₂ := eq28446
       grind)
    | exact resolve eq67989 eq28446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28446 eq67989
  have eq68024 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq68017
       grind)
    | exact superpose eq68017 eq22
    | exact resolve eq22 eq68017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq68017
  have eq68273 : (σ x) = (σ y) := by
    first
    | exact superpose eq68024 eq28397
    | exact resolve eq28397 eq68024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28397
  have eq68274 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq68024 eq20
    | exact resolve eq20 eq68024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq68024
  have eq68431 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq68273 eq26
    | exact resolve eq26 eq68273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq68839 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq68274 eq17164
    | exact resolve eq17164 eq68274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17164
  have eq68860 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq68839
       have r₂ := eq7503
       grind)
    | exact resolve eq68839 eq7503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7503 eq68839
  have eq68876 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq68431 eq68860
    | exact resolve eq68860 eq68431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68431 eq68860
  have eq68888 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq68273 eq68876
    | exact resolve eq68876 eq68273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68273 eq68876
  have eq68889 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq68888
  have eq68919 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq68889 eq27
    | exact resolve eq27 eq68889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq68889
  have eq69063 : False := by grind
  exact eq69063

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X0 ∨ (k X2 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq86 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq93 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq76
    | (have j0 := eq76 (σ x) (σ X0)
       grind)
    | exact resolve eq76 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
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
  have eq100 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
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
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq76 y y
       grind)
    | exact superpose eq76 eq74
    | (have j1 := eq76 y y
       grind)
    | exact resolve eq74 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq108 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq119 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
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
  have eq131 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq76 sF1 (σ X0)
       grind)
    | exact superpose eq76 eq37
    | (have j1 := eq76 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  have eq186 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq76 (σ X0) sF3
       grind)
    | exact superpose eq76 eq40
    | (have j1 := eq76 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
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
  have eq222 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq674 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
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
  have eq729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq76
    | (have j0 := eq76 (σ y) (σ x)
       grind)
    | exact resolve eq76 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq729
    | exact resolve eq729 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq733 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq730
       have r₂ := eq27
       grind)
    | exact resolve eq730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq735 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq733 eq54
    | exact resolve eq54 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq736 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq733 eq51
    | exact resolve eq51 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq733 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq733
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq733
       grind)
    | exact resolve eq12 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq733 eq56
    | exact resolve eq56 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq744 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq737
  have eq748 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq387 eq736
    | (have j0 := eq736 (σ x)
       grind)
    | exact resolve eq736 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq783 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq92 X0 X0
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq92 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq92 X1 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (σ X0) X2) (M.op X3 (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (σ X0) X2 X3 (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq14
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq14 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X1) (M.op X2 (M.op X3 (σ (k X0 X1))))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (σ X1) (σ X0) x x
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq52
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq52 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq793 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq783 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq783 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq783 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq805 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq748 eq212
    | exact resolve eq212 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 X2) ≠ (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) ∨ (k X5 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2)))) = (M.op (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) X5) := by
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
  have eq1034 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq733 eq385
    | exact resolve eq385 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq733
  have eq1367 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq744 eq110
    | exact resolve eq110 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq1370 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1367
  have eq1378 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1370 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1370
       grind)
    | exact resolve eq13 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1391 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq2292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1391 eq110
    | exact resolve eq110 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq1391
  have eq2302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq2292
  have eq2308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq2302
    | exact resolve eq2302 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302
  have eq2310 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq2308
       have r₂ := eq27
       grind)
    | exact resolve eq2308 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq2362 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2310 eq805
    | exact resolve eq805 eq2310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2368 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq2310 eq52
    | exact resolve eq52 eq2310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2377 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq2362
  have eq3005 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2377 eq2368
    | exact resolve eq2368 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2368 eq2377
  have eq3046 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq3005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005
  have eq3129 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq93 eq805
    | (have j1 := eq93 X0
       grind)
    | exact resolve eq805 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3131 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (k x X0))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq93 eq1034
    | (have j1 := eq93 X0
       grind)
    | exact resolve eq1034 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1034
  have eq4345 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq791 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq791
    | (have j0 := eq791 (τ X0)
       grind)
    | exact resolve eq791 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq4346 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq791 x
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq791
    | (have j0 := eq791 x
       grind)
    | exact resolve eq791 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq4351 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4346
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4346
    | exact resolve eq4346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4346
  have eq4352 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4345 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4345
    | (have j0 := eq4345 X0
       grind)
    | exact resolve eq4345 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4345
  have eq4356 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4351
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4351
    | exact resolve eq4351 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4351
  have eq4357 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4352 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4352
    | (have j0 := eq4352 X0
       grind)
    | exact resolve eq4352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4352
  have eq4835 : ∀ X0 : G, (σ y) = (M.op (σ (k X0 y)) (σ x)) ∨ y = (M.op y x) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq186 eq743
    | (have j1 := eq186 X0
       grind)
    | exact resolve eq743 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq743
  have eq5619 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k (M.op x y) X0)) (M.op X1 (σ (k X0 X2)))) ∨ (σ X0) = (M.op (σ X0) (σ X2)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq131 eq786
    | (have j0 := eq786 X0 X2 X2 x
       have j1 := eq131 X0
       grind)
    | exact resolve eq786 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq786
  have eq7122 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X0 (M.op X1 (k (σ x) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq787 x x x x
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq787
    | (have j0 := eq787 x x x x
       grind)
    | exact resolve eq787 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq787
  have eq7194 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X0 (M.op X1 (k (σ x) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq7122 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7122
    | (have j0 := eq7122 X0 X1
       grind)
    | exact resolve eq7122 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7122
  have eq7229 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X0 (M.op X1 (k (σ x) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq7194 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7194
    | (have j0 := eq7194 X0 X1
       grind)
    | exact resolve eq7194 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7194
  have eq11147 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3129 y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3129
    | (have j0 := eq3129 y
       grind)
    | exact resolve eq3129 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129
  have eq11190 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11147
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11147
    | exact resolve eq11147 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11147
  have eq11197 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq11190
    | exact resolve eq11190 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11190
  have eq15086 : (σ y) = (M.op (k (σ x) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4835 x
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq4835
    | (have j0 := eq4835 x
       grind)
    | exact resolve eq4835 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq4835
  have eq15159 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq15086
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15086
    | exact resolve eq15086 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15086
  have eq15167 : (σ y) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15159
    | exact resolve eq15159 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15159
  have eq15188 : ∀ X0 X1 : G, (k (σ x) (σ y)) = (M.op (σ y) (M.op X0 (M.op X1 (k (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq15167 eq14
    | exact resolve eq14 eq15167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15167
  have eq29500 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (k (σ x) X0)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3131 (τ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq3131
    | (have j0 := eq3131 (τ X0) X1
       grind)
    | exact resolve eq3131 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq3131
  have eq29723 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (k (σ x) X0)) ∨ (σ x) = (M.op (σ x) X0) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq29500 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq29500
    | (have j0 := eq29500 X0 X1
       grind)
    | exact resolve eq29500 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29500
  have eq33270 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq11197 eq15188
    | exact resolve eq15188 eq11197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11197 eq15188
  have eq33369 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq33270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33270
  have eq33542 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq33369 eq735
    | exact resolve eq735 eq33369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq33369
  have eq33628 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33542
  have eq33679 : (τ (σ y)) = (k x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33628 eq60
    | exact resolve eq60 eq33628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33628
  have eq33717 : y = (k x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq33679
    | exact resolve eq33679 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33679
  have eq33852 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76 x y
       have i₂ := eq33717
       grind)
    | exact superpose eq33717 eq76
    | (have j0 := eq76 y x
       grind)
    | exact resolve eq76 eq33717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33717
  have eq33864 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33852
  have eq33878 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33864
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33864
    | exact resolve eq33864 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33864
  have eq33906 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq33878
       grind)
    | exact superpose eq33878 eq108
    | exact resolve eq108 eq33878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33909 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq33878
       grind)
    | exact superpose eq33878 eq50
    | exact resolve eq50 eq33878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33878
  have eq33934 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33906
  have eq33945 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33909 x
       have i₂ := eq386 sF0 x
       grind)
    | (have i₁ := eq33909 x
       have i₂ := eq386 sF0 x
       grind)
    | exact superpose eq386 eq33909
    | (have j0 := eq33909 x
       grind)
    | exact resolve eq33909 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33909
  have eq33946 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33934
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33934
    | exact resolve eq33934 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33934
  have eq34127 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33946 eq76
    | (have j0 := eq76 (σ y) (σ x)
       grind)
    | exact resolve eq76 eq33946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33946
  have eq34147 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq34127
    | exact resolve eq34127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34127
  have eq34148 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq34147
  have eq34158 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34148 eq51
    | exact resolve eq51 eq34148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34148
  have eq34221 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq387 eq34158
    | (have j0 := eq34158 (σ x)
       grind)
    | exact resolve eq34158 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34158
  have eq34434 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34221 eq212
    | exact resolve eq212 eq34221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq34221
  have eq36858 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33945 eq161
    | exact resolve eq161 eq33945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq33945
  have eq36919 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq36858
  have eq36921 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36919
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36919
    | exact resolve eq36919 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36919
  have eq36923 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36921 eq164
    | exact resolve eq164 eq36921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36949 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq36923
    | exact resolve eq36923 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq36923
  have eq144865 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X1 (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq29723 eq7229
    | (have j1 := eq29723 (σ x) X1
       grind)
    | exact resolve eq7229 eq29723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7229 eq29723
  have eq144985 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X1 (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq144865 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144865
  have eq145008 : ∀ X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X1 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X1
    first
    | exact superpose eq387 eq144985
    | (have j0 := eq144985 (σ x) X1
       grind)
    | exact resolve eq144985 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144985
  have eq145037 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq145008 eq3046
    | exact resolve eq3046 eq145008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046 eq145008
  have eq145158 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq145037
  have eq145364 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq145158 eq805
    | exact resolve eq805 eq145158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145158
  have eq145451 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq145364
  have eq145785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq145451 eq2310
    | exact resolve eq2310 eq145451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145451
  have eq145914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq145785
  have eq145927 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq145914
       have r₂ := eq27
       grind)
    | exact resolve eq145914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145914
  have eq146074 : (τ (σ (M.op x y))) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq145927 eq49
    | exact resolve eq49 eq145927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq146075 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq145927 eq4356
    | exact resolve eq4356 eq145927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4356 eq145927
  have eq146144 : (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq146074
    | exact resolve eq146074 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146074
  have eq146147 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq146144
       have i₂ := eq76 x x
       grind)
    | exact superpose eq76 eq146144
    | (have j1 := eq76 y x
       grind)
    | exact resolve eq146144 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146170 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4357 x
       have i₂ := eq146144
       grind)
    | exact superpose eq146144 eq4357
    | (have j0 := eq4357 x
       grind)
    | exact resolve eq4357 eq146144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4357 eq146144
  have eq148173 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op X2 (M.op x y)))) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq674 X2 x x X0 X1
       have i₂ := eq146147
       grind)
    | exact superpose eq146147 eq674
    | exact resolve eq674 eq146147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146147
  have eq148202 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq406 eq148173
    | exact resolve eq148173 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq148173
  have eq177666 : (k (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq148202 y
       grind)
    | exact superpose eq148202 eq101
    | exact resolve eq101 eq148202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq148202
  have eq177750 : (k (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq177666
  have eq213318 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq177750
       grind)
    | exact superpose eq177750 eq108
    | exact resolve eq108 eq177750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213340 : (τ (k (σ y) (σ y))) = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq177750
       grind)
    | exact superpose eq177750 eq16
    | exact resolve eq16 eq177750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177750
  have eq213467 : (k y y) = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq86 eq213340
    | exact resolve eq213340 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213340
  have eq213470 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq213318
       have r₂ := eq146170
       grind)
    | exact resolve eq213318 eq146170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213318
  have eq213555 : (τ (k (σ x) (σ y))) = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq213470 eq86
    | exact resolve eq86 eq213470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213470
  have eq213623 : (k x y) = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq60 eq213555
    | exact resolve eq213555 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213555
  have eq213642 : (k x y) = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq213467
       have i₂ := eq213623
       grind)
    | exact superpose eq213623 eq213467
    | exact resolve eq213467 eq213623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213467 eq213623
  have eq213669 : (k x y) = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq213642
  have eq619473 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq36949 eq5619
    | (have j0 := eq5619 (M.op x y) x (M.op x y)
       grind)
    | exact resolve eq5619 eq36949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5619
  have eq620625 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq619473 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq619473
    | (have j0 := eq619473 X0
       grind)
    | exact resolve eq619473 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619473
  have eq621249 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq620625
    | (have j0 := eq620625 X0
       grind)
    | exact resolve eq620625 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620625
  have eq621822 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq621249
    | (have j0 := eq621249 X0
       grind)
    | exact resolve eq621249 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621249
  have eq622365 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq621822
    | (have j0 := eq621822 X0
       grind)
    | exact resolve eq621822 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621822
  have eq622366 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq622365 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622365
  have eq623163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq622366 eq34434
    | exact resolve eq34434 eq622366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34434 eq622366
  have eq623309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq623163
  have eq623348 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq623309
       have r₂ := eq27
       grind)
    | exact resolve eq623309 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623309
  have eq627609 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq623348 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq623348
       grind)
    | exact resolve eq13 eq623348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627650 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq627609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627609
  have eq639376 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq627650 eq164
    | exact resolve eq164 eq627650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq639394 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq627650 eq36921
    | exact resolve eq36921 eq627650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36921 eq627650
  have eq640028 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq639394
  have eq640138 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq640028 eq623348
    | exact resolve eq623348 eq640028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640028
  have eq640248 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq640138
  have eq640270 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq640248 eq748
    | exact resolve eq748 eq640248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748 eq640248
  have eq640405 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq640270
       have r₂ := eq146075
       grind)
    | exact resolve eq640270 eq146075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146075 eq640270
  have eq645046 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq640405 eq2310
    | exact resolve eq2310 eq640405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645185 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq640405 eq805
    | exact resolve eq805 eq640405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq640405
  have eq645319 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq645185
  have eq645455 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq645046
  have eq645522 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq645455
       grind)
    | exact superpose eq645455 eq108
    | exact resolve eq108 eq645455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645455
  have eq645691 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq645522
  have eq645711 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq645691
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq645691
    | exact resolve eq645691 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645691
  have eq648463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq645319 eq2310
    | exact resolve eq2310 eq645319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310 eq645319
  have eq648885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq648463
  have eq648905 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq648885
       have r₂ := eq27
       grind)
    | exact resolve eq648885 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648885
  have eq649995 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq648905
       grind)
    | exact superpose eq648905 eq108
    | exact resolve eq108 eq648905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq650056 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq648905
       grind)
    | exact superpose eq648905 eq53
    | exact resolve eq53 eq648905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq650079 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op X2 y))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq674 X2 y x X0 X1
       have i₂ := eq648905
       grind)
    | exact superpose eq648905 eq674
    | exact resolve eq674 eq648905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq648905
  have eq650166 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq649995
  have eq650177 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq650079 X0 X1 x
       have i₂ := eq386 X1 x
       grind)
    | (have i₁ := eq650079 X0 X0 x
       have i₂ := eq386 X0 X1
       grind)
    | exact superpose eq386 eq650079
    | (have j0 := eq650079 X0 X1 x
       grind)
    | exact resolve eq650079 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650079
  have eq650207 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq650166
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq650166
    | exact resolve eq650166 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq650166
  have eq651427 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq650207 eq60
    | exact resolve eq60 eq650207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq650207
  have eq651600 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq651427
    | exact resolve eq651427 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651427
  have eq651734 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq213669
       have i₂ := eq651600
       grind)
    | exact superpose eq651600 eq213669
    | exact resolve eq213669 eq651600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213669 eq651600
  have eq651790 : y = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq651734
  have eq651849 : y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq651790
       have r₂ := eq146170
       grind)
    | exact resolve eq651790 eq146170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146170 eq651790
  have eq657780 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq651849
       grind)
    | exact superpose eq651849 eq50
    | exact resolve eq50 eq651849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq657789 : y ≠ y ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq651849
       grind)
    | exact superpose eq651849 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq651849
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq651849
       grind)
    | exact resolve eq12 eq651849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651849
  have eq657826 : y ≠ y ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by grind
  clear eq657789
  have eq657827 : (k y x) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq657826
  have eq657850 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq657780 x
       have i₂ := eq386 sF0 x
       grind)
    | (have i₁ := eq657780 x
       have i₂ := eq386 sF0 x
       grind)
    | exact superpose eq386 eq657780
    | (have j0 := eq657780 x
       grind)
    | exact resolve eq657780 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657780
  have eq678944 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq657827
       grind)
    | exact superpose eq657827 eq73
    | exact resolve eq73 eq657827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657827
  have eq688432 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq623348 eq639376
    | exact resolve eq639376 eq623348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623348 eq639376
  have eq688842 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq688432
  have eq688850 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq688842
    | exact resolve eq688842 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq688842
  have eq688875 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq688850 eq36949
    | exact resolve eq36949 eq688850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36949 eq688850
  have eq688991 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq688875
  have eq689108 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq688991 eq27
    | exact resolve eq27 eq688991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689111 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq688991 eq119
    | (have r₁ := eq119
       have r₂ := eq688991
       grind)
    | exact resolve eq119 eq688991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq689114 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq688991 eq222
    | exact resolve eq222 eq688991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689245 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq689111
  have eq689484 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq689114 eq387
    | exact resolve eq387 eq689114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689114
  have eq854602 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq689245 eq645711
    | exact resolve eq645711 eq689245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645711 eq689245
  have eq854702 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq854602
  have eq854774 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq854702
       have r₂ := eq689108
       grind)
    | exact resolve eq854702 eq689108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689108 eq854702
  have eq854805 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq854774 eq387
    | exact resolve eq387 eq854774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq854815 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq854774 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq854774
       grind)
    | exact resolve eq13 eq854774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854856 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq854815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854815
  have eq857074 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq854805 eq689484
    | exact resolve eq689484 eq854805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689484 eq854805
  have eq857484 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq857074 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857074
  have eq867125 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq854856 eq86
    | exact resolve eq86 eq854856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq854856
  have eq869408 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq222 eq857484
    | exact resolve eq857484 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq857484
  have eq873395 : ∀ X1 X2 X3 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 (σ x)))) ∨ (k X3 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 (σ x))))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 (σ x)))) X3) ∨ x = (M.op x y) := by
    intro X1 X2 X3
    first
    | exact superpose eq869408 eq874
    | exact resolve eq874 eq869408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq869408
  have eq873477 : ∀ X1 X2 X3 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X3 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 (σ x))))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 (σ x)))) X3) ∨ x = (M.op x y) := by
    intro X1 X2 X3
    first
    | exact superpose eq51 eq873395
    | (have j0 := eq873395 X1 X2 X3
       grind)
    | exact resolve eq873395 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873395
  have eq873484 : ∀ X1 X2 X3 : G, (k X3 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 (σ x))))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 (σ x)))) X3) ∨ x = (M.op x y) := by
    intro X1 X2 X3
    first
    | (have j0 := eq873477 X1 X2 X3
       grind)
    | (have r₁ := eq873477 X1 X2 X3
       have r₂ := eq688991
       grind)
    | exact resolve eq873477 eq688991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688991 eq873477
  have eq873486 : ∀ X3 : G, (M.op (σ x) X3) = (k X3 (σ x)) ∨ x = (M.op x y) := by
    intro X3
    first
    | exact superpose eq51 eq873484
    | exact resolve eq873484 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq873484
  have eq884103 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq873486 eq81
    | exact resolve eq81 eq873486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq873486
  have eq884842 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq884103
    | exact resolve eq884103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884103
  have eq884882 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq884842
       grind)
    | exact superpose eq884842 eq73
    | exact resolve eq73 eq884842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884842
  have eq885063 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq884882
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq884882
    | exact resolve eq884882 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884882
  have eq889840 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq854774 eq867125
    | exact resolve eq867125 eq854774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854774 eq867125
  have eq890272 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) := by grind
  clear eq889840
  have eq890278 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq890272
    | exact resolve eq890272 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq890272
  have eq890345 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76 y y
       have i₂ := eq890278
       grind)
    | exact superpose eq890278 eq76
    | (have j0 := eq76 y y
       grind)
    | exact resolve eq76 eq890278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq890278
  have eq890379 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq890345
  have eq890561 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq386 X0 y
       have i₂ := eq890379
       grind)
    | exact superpose eq890379 eq386
    | exact resolve eq386 eq890379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890379
  have eq893917 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq890561 eq650056
    | exact resolve eq650056 eq890561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650056
  have eq893918 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op X0 y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq890561 eq650177
    | exact resolve eq650177 eq890561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650177 eq890561
  have eq894328 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq893918 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893918
  have eq894329 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq893917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893917
  have eq894401 : ∀ X1 : G, (M.op X1 x) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq894328 x X1
       have i₂ := eq386 X1 x
       grind)
    | (have i₁ := eq894328 x x
       have i₂ := eq386 x X1
       grind)
    | exact superpose eq386 eq894328
    | (have j0 := eq894328 x X1
       grind)
    | exact resolve eq894328 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894328
  have eq894402 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq894329 x
       have i₂ := eq386 y x
       grind)
    | (have i₁ := eq894329 x
       have i₂ := eq386 y x
       grind)
    | exact superpose eq386 eq894329
    | (have j0 := eq894329 x
       grind)
    | exact resolve eq894329 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894329
  have eq898416 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq894402 eq208
    | exact resolve eq208 eq894402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq894402
  have eq898533 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq898416 x
       have i₂ := eq386 x x
       grind)
    | (have i₁ := eq898416 x
       have i₂ := eq386 x x
       grind)
    | exact superpose eq386 eq898416
    | (have j0 := eq898416 x
       grind)
    | exact resolve eq898416 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq898416
  have eq900049 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq894401 eq898533
    | exact resolve eq898533 eq894401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894401 eq898533
  have eq900203 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq900049
  have eq900380 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq678944
       have i₂ := eq900203
       grind)
    | exact superpose eq900203 eq678944
    | exact resolve eq678944 eq900203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678944 eq900203
  have eq900491 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq900380
  have eq900501 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq900491
    | exact resolve eq900491 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900491
  have eq900703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq900501 eq885063
    | exact resolve eq885063 eq900501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885063 eq900501
  have eq900757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq900703
  have eq900763 : x = (M.op x y) := by
    first
    | (have r₁ := eq900757
       have r₂ := eq27
       grind)
    | exact resolve eq900757 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900757
  have eq900771 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq900763 eq20
    | exact resolve eq20 eq900763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901081 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq900763 eq657850
    | exact resolve eq657850 eq900763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657850 eq900763
  have eq901084 : x = (M.op x x) := by grind
  clear eq901081
  have eq901239 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq900771
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq900771
    | exact resolve eq900771 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900771
  have eq901242 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq901239 eq26
    | exact resolve eq26 eq901239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq902450 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq901084
       grind)
    | exact superpose eq901084 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq901084
       grind)
    | exact resolve eq13 eq901084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902495 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq902450 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902450
  have eq903720 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq902495 y
       grind)
    | exact superpose eq902495 eq73
    | exact resolve eq73 eq902495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq903782 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq793 x X0
       have i₂ := eq902495 x
       grind)
    | exact superpose eq902495 eq793
    | (have j0 := eq793 x X0
       grind)
    | exact resolve eq793 eq902495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq902495
  have eq904686 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq903782 X0
       have i₂ := eq901084
       grind)
    | exact superpose eq901084 eq903782
    | (have j0 := eq903782 X0
       grind)
    | exact resolve eq903782 eq901084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901084 eq903782
  have eq904687 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq904686 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904686
  have eq904727 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq901239 eq903720
    | exact resolve eq903720 eq901239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903720
  have eq905293 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq904687 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq904687
    | (have j0 := eq904687 X0
       grind)
    | exact resolve eq904687 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq904687
  have eq905331 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq904727
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq904727
    | exact resolve eq904727 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq904727
  have eq905678 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq901239 eq905293
    | exact resolve eq905293 eq901239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901239 eq905293
  have eq905716 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq905331
    | exact resolve eq905331 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq905331
  have eq907979 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq905678 eq905716
    | exact resolve eq905716 eq905678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905678 eq905716
  have eq908709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq901242 eq907979
    | exact resolve eq907979 eq901242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901242 eq907979
  have eq908881 : False := by grind
  exact eq908881

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxy_pxx_pyx_Equation1473 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq606 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2422 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (M.op (σ X0) (σ X1)) (M.op X2 (M.op X3 (σ X1)))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2 X3
       have i₂ := eq606 X0 X1
       grind)
    | (have i₁ := eq9 (σ X0) (σ X1) X2 X3
       have i₂ := eq606 X0 X1
       grind)
    | exact superpose eq606 eq9
    | (have j1 := eq606 X0 X1
       grind)
    | exact resolve eq9 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2423 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (σ X0) X2) (M.op X3 (M.op (σ X0) (σ X1)))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (σ X0) X2 X3 (σ X1)
       have i₂ := eq606 X0 X1
       grind)
    | (have i₁ := eq9 (σ X1) X1 X2 (σ X0)
       have i₂ := eq606 X0 X1
       grind)
    | exact superpose eq606 eq9
    | (have j1 := eq606 X0 X1
       grind)
    | exact resolve eq9 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq31614 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2422 X0 X1 x (σ X0)
       have i₂ := eq2423 X0 X1 (σ X1) x
       grind)
    | exact superpose eq2423 eq2422
    | (have j0 := eq2422 X0 X1 x x
       have j1 := eq2423 X0 X1 x x
       grind)
    | exact resolve eq2422 eq2423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422 eq2423
  have eq31813 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq31614 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31614
  have eq32067 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31813 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq31813
    | (have j0 := eq31813 (τ X0) (τ X1)
       grind)
    | exact resolve eq31813 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq32142 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32067 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32067
    | (have j0 := eq32067 X0 X1
       grind)
    | exact resolve eq32067 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32067
  have eq32159 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32142 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq32142
    | (have j0 := eq32142 X0 X1
       grind)
    | exact resolve eq32142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32142
  have eq32164 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32159 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq32159
    | (have j0 := eq32159 X0 X1
       grind)
    | exact resolve eq32159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32159
  have eq32169 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32164 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq32164
    | (have j0 := eq32164 X0 X1
       grind)
    | exact resolve eq32164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32164
  have eq32174 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32169 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32169
    | (have j0 := eq32169 X0 X1
       grind)
    | exact resolve eq32169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32169
  have eq32181 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31813 X1 X0
       have i₂ := eq32174 X1 X0
       grind)
    | exact superpose eq32174 eq31813
    | (have j0 := eq31813 X0 X1
       have j1 := eq32174 (σ (M.op X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq31813 eq32174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31813 eq32174
  have eq167018 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq32181 x y
       grind)
    | exact superpose eq32181 eq16
    | (have j1 := eq32181 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq32181 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq32181 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq32181 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq32181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32181
  have eq167280 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq167018
  have eq167478 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq167280
       grind)
    | exact superpose eq167280 eq10
    | exact resolve eq10 eq167280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167280
  have eq167584 : x = y ∨ x = y := by
    first
    | (have i₁ := eq167478
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq167478
    | exact resolve eq167478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167478
  have eq167585 : x = y := by grind
  clear eq167584
  have eq167594 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq167585
       grind)
    | exact superpose eq167585 eq16
    | exact resolve eq16 eq167585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167585
  have eq167595 : False := by grind
  exact eq167595

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pyy_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq77 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
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
  have eq80 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq188 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq78 X1 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq196 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq198 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq196 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq196 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq201 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq450 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq483 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq450
    | (have j0 := eq450 X0 X1
       grind)
    | exact resolve eq450 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq912 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ X1)) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq192 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq192
    | (have j0 := eq192 (σ X1) (σ X0)
       grind)
    | exact resolve eq192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq1451 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ X1)) ∨ (σ (σ (k X0 X1))) = (M.op (σ (σ X1)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq201
    | (have j0 := eq201 (σ (k X0 X1)) (σ X1)
       grind)
    | exact resolve eq201 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq4237 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4262 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq79 (σ X1) X1
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4264 : ∀ X0 X1 X2 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (M.op X2 X0) (M.op X0 (σ X1))) = X0 ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X1) X1 X0
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq21
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq21 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4285 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq4286 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4285 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285
  have eq4288 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4262 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4262
  have eq4289 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq4288 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288
  have eq4291 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4286 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4286
    | (have j0 := eq4286 X0
       grind)
    | exact resolve eq4286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4286
  have eq4300 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4237 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq4237
    | (have j0 := eq4237 X0 X1
       grind)
    | exact resolve eq4237 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4237
  have eq4322 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq4291 X0
       grind)
    | exact superpose eq4291 eq39
    | (have j1 := eq4291 X0
       grind)
    | exact resolve eq39 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq4291
  have eq4343 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4322 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4322
    | (have j0 := eq4322 X0
       grind)
    | exact resolve eq4322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4322
  have eq4344 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4343
  have eq4346 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4344 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4344
    | exact resolve eq4344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4371 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4344 X0
       grind)
    | exact superpose eq4344 eq11
    | exact resolve eq11 eq4344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4344
  have eq4431 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4346 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq4346
    | exact resolve eq4346 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4346
  have eq4516 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4431 X0
       grind)
    | exact superpose eq4431 eq11
    | exact resolve eq11 eq4431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4625 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4516 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4516
    | exact resolve eq4516 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4516
  have eq4688 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq4625 (τ X0)
       grind)
    | exact superpose eq4625 eq35
    | exact resolve eq35 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4743 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4688 X0
       have i₂ := eq4431 X0
       grind)
    | exact superpose eq4431 eq4688
    | exact resolve eq4688 eq4431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4431 eq4688
  have eq5320 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5349 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5320 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5320
    | exact resolve eq5320 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5320
  have eq5385 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5349 X0
       have i₂ := eq4625 X0
       grind)
    | exact superpose eq4625 eq5349
    | exact resolve eq5349 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349
  have eq5405 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5385
  have eq6295 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (k X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq77 X0 (σ X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (σ X0) (σ X0))
       have r₂ := eq77 X0 (M.op (M.op (σ X0) (σ X0)) X0)
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq6319 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (k X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6295
  have eq6320 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (k X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6319 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6319
  have eq6345 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6320 X0 X1
       have i₂ := eq4371 X0
       grind)
    | exact superpose eq4371 eq6320
    | (have j0 := eq6320 X0 X1
       grind)
    | exact resolve eq6320 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320
  have eq6387 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6345 X0 X1
       have i₂ := eq4625 X0
       grind)
    | exact superpose eq4625 eq6345
    | (have j0 := eq6345 X0 X1
       grind)
    | exact resolve eq6345 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345
  have eq6414 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6387 X0 X1
       have i₂ := eq4371 X0
       grind)
    | exact superpose eq4371 eq6387
    | (have j0 := eq6387 X0 X1
       grind)
    | exact resolve eq6387 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq6432 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6414 X0 X1
       have i₂ := eq4625 X0
       grind)
    | exact superpose eq4625 eq6414
    | (have j0 := eq6414 X0 X1
       grind)
    | exact resolve eq6414 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6414
  have eq16492 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4300 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4300
    | (have j0 := eq4300 (σ X0) (σ X1)
       grind)
    | exact resolve eq4300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4300
  have eq16696 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16492 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq16492
    | (have j0 := eq16492 X0 X1
       grind)
    | exact resolve eq16492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16492
  have eq16718 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16696 X0 X1
       have i₂ := eq4371 X1
       grind)
    | exact superpose eq4371 eq16696
    | (have j0 := eq16696 X0 X1
       grind)
    | exact resolve eq16696 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16696
  have eq16738 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16718 X0 X1
       have i₂ := eq4625 X1
       grind)
    | exact superpose eq4625 eq16718
    | (have j0 := eq16718 X0 X1
       grind)
    | exact resolve eq16718 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16718
  have eq34357 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq912 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq912
    | (have j0 := eq912 (τ X0) (τ X1)
       grind)
    | exact resolve eq912 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq34429 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34357 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq34357
    | (have j0 := eq34357 X0 X1
       grind)
    | exact resolve eq34357 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34357
  have eq34480 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34429 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq34429
    | (have j0 := eq34429 X0 X1
       grind)
    | exact resolve eq34429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34429
  have eq34529 : ∀ X0 X1 : G, (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34480 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34480
    | (have j0 := eq34480 X0 X1
       grind)
    | exact resolve eq34480 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34480
  have eq34576 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34529 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34529
    | (have j0 := eq34529 X0 X1
       grind)
    | exact resolve eq34529 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34529
  have eq34616 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34576 X0 X1
       have i₂ := eq4371 (σ (τ X1))
       grind)
    | exact superpose eq4371 eq34576
    | (have j0 := eq34576 X0 X1
       grind)
    | exact resolve eq34576 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34576
  have eq34654 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34616 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq34616
    | (have j0 := eq34616 X0 X1
       grind)
    | exact resolve eq34616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34616
  have eq34690 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34654 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq34654
    | (have j0 := eq34654 X0 X1
       grind)
    | exact resolve eq34654 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34654
  have eq34719 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34690 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq34690
    | (have j0 := eq34690 X0 X1
       grind)
    | exact resolve eq34690 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34690
  have eq34744 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34719 X0 X1
       have i₂ := eq4625 X1
       grind)
    | exact superpose eq4625 eq34719
    | (have j0 := eq34719 X0 X1
       grind)
    | exact resolve eq34719 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34719
  have eq34769 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34744 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34744
    | (have j0 := eq34744 X0 X1
       grind)
    | exact resolve eq34744 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34744
  have eq50936 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1451 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq1451
    | (have j0 := eq1451 (τ (k X0 X1)) (τ X1)
       grind)
    | exact resolve eq1451 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq51019 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50936 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq50936
    | (have j0 := eq50936 X0 X1
       grind)
    | exact resolve eq50936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50936
  have eq51078 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51019 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq51019
    | (have j0 := eq51019 X0 X1
       grind)
    | exact resolve eq51019 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51019
  have eq51137 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51078 X0 X1
       have i₂ := eq4371 (σ (τ X1))
       grind)
    | exact superpose eq4371 eq51078
    | (have j0 := eq51078 X0 X1
       grind)
    | exact resolve eq51078 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51078
  have eq51195 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51137 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq51137
    | (have j0 := eq51137 X0 X1
       grind)
    | exact resolve eq51137 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51137
  have eq51253 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) = (σ (k (σ (τ X1)) X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51195 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq51195
    | (have j0 := eq51195 X0 X1
       grind)
    | exact resolve eq51195 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51195
  have eq51311 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ (k X0 X1)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51253 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq51253
    | (have j0 := eq51253 X0 X1
       grind)
    | exact resolve eq51253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51253
  have eq51364 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51311 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq51311
    | (have j0 := eq51311 X0 X1
       grind)
    | exact resolve eq51311 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51311
  have eq51410 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51364 X0 X1
       have i₂ := eq4625 X1
       grind)
    | exact superpose eq4625 eq51364
    | (have j0 := eq51364 X0 X1
       grind)
    | exact resolve eq51364 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51364
  have eq51448 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51410 X0 X1
       have i₂ := eq4371 (σ (τ X1))
       grind)
    | exact superpose eq4371 eq51410
    | (have j0 := eq51410 X0 X1
       grind)
    | exact resolve eq51410 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51410
  have eq51481 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51448 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq51448
    | (have j0 := eq51448 X0 X1
       grind)
    | exact resolve eq51448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51448
  have eq51509 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51481 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq51481
    | (have j0 := eq51481 X0 X1
       grind)
    | exact resolve eq51481 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq51481
  have eq51535 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51509 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq51509
    | (have j0 := eq51509 X0 X1
       grind)
    | exact resolve eq51509 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51509
  have eq51561 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51535 X0 X1
       have i₂ := eq4625 X1
       grind)
    | exact superpose eq4625 eq51535
    | (have j0 := eq51535 X0 X1
       grind)
    | exact resolve eq51535 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51535
  have eq51585 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51561 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51561
    | (have j0 := eq51561 X0 X1
       grind)
    | exact resolve eq51561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51561
  have eq51708 : ∀ X0 X1 : G, (σ X1) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (τ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51585 (τ X0) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq51585
    | (have j0 := eq51585 (τ X0) X1
       grind)
    | exact resolve eq51585 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51585
  have eq51734 : ∀ X0 X1 : G, (σ X1) ≠ (k X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51708 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51708
    | (have j0 := eq51708 X0 X1
       grind)
    | exact resolve eq51708 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51708
  have eq125529 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4289 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4289
    | exact resolve eq4289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4289
  have eq125840 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq125529 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq125529
    | (have j0 := eq125529 X0 X1
       grind)
    | exact resolve eq125529 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125529
  have eq126205 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq125840 X1 X0
       grind)
    | exact superpose eq125840 eq11
    | (have j1 := eq125840 X1 X0
       grind)
    | exact resolve eq11 eq125840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125840
  have eq126436 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq126205 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq126205
    | (have j0 := eq126205 X0 X1
       grind)
    | exact resolve eq126205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126205
  have eq128286 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 X0) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq126436 X0 (τ X1)
       grind)
    | exact superpose eq126436 eq18
    | (have j1 := eq126436 X0 (τ X1)
       grind)
    | exact resolve eq18 eq126436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128448 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq126436 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126436
  have eq129744 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq128448 X0 (σ X0)
       have i₂ := eq4371 X0
       grind)
    | exact superpose eq4371 eq128448
    | exact resolve eq128448 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128448
  have eq129814 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq129744 X0 X1
       have i₂ := eq4625 X0
       grind)
    | exact superpose eq4625 eq129744
    | (have j0 := eq129744 X0 X1
       grind)
    | exact resolve eq129744 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129744
  have eq129916 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (M.op (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq129814 X0 X1
       have i₂ := eq4625 X0
       grind)
    | exact superpose eq4625 eq129814
    | (have j0 := eq129814 X0 X1
       grind)
    | exact resolve eq129814 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129814
  have eq130012 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq129916 X0 X1
       have i₂ := eq4625 X0
       grind)
    | exact superpose eq4625 eq129916
    | (have j0 := eq129916 X0 X1
       grind)
    | exact resolve eq129916 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129916
  have eq134637 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq128286 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq128286
    | exact resolve eq128286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128286
  have eq135089 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq134637 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq134637
    | (have j0 := eq134637 X0 X1
       grind)
    | exact resolve eq134637 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134637
  have eq136043 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135089 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq135089
    | (have j0 := eq135089 (τ X0) (τ X1)
       grind)
    | exact resolve eq135089 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135089
  have eq136571 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136043 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq136043
    | (have j0 := eq136043 X0 X1
       grind)
    | exact resolve eq136043 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136043
  have eq136731 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136571 X0 X1
       have i₂ := eq4743 X1
       grind)
    | exact superpose eq4743 eq136571
    | (have j0 := eq136571 X0 X1
       grind)
    | exact resolve eq136571 eq4743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136571
  have eq136826 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq136731 X0 X1
       have i₂ := eq4743 X1
       grind)
    | exact superpose eq4743 eq136731
    | (have j0 := eq136731 X0 X1
       grind)
    | exact resolve eq136731 eq4743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4743 eq136731
  have eq171105 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq6432 X1 X0
       grind)
    | exact superpose eq6432 eq11
    | (have j1 := eq6432 X1 X0
       grind)
    | exact resolve eq11 eq6432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6432
  have eq171280 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq171105 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq171105
    | (have j0 := eq171105 X0 X1
       grind)
    | exact resolve eq171105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq171105
  have eq173233 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51734 X0 X1
       have i₂ := eq171280 X0 X1
       grind)
    | exact superpose eq171280 eq51734
    | (have j0 := eq51734 X1 X0
       have j1 := eq171280 X1 X0
       grind)
    | (have r₁ := eq51734 X0 (M.op X1 X1)
       have r₂ := eq171280 (k X0 (σ (M.op X1 X1))) X1
       grind)
    | exact resolve eq51734 eq171280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51734 eq171280
  have eq173442 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq173233 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173233
  have eq173592 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq173442 X0 X1
       have j1 := eq130012 X0 X1
       grind)
    | (have r₁ := eq173442 (M.op X0 X0) X1
       have r₂ := eq130012 X0 (M.op (σ (M.op X0 X0)) X1)
       grind)
    | (have r₁ := eq173442 X0 (M.op (σ X0) X1)
       have r₂ := eq130012 X0 X1
       grind)
    | (have r₁ := eq173442 X0 X1
       have r₂ := eq130012 X0 X1
       grind)
    | exact resolve eq173442 eq130012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130012 eq173442
  have eq182774 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq16738 X0 X1
       grind)
    | exact superpose eq16738 eq11
    | (have j1 := eq16738 X0 X1
       grind)
    | exact resolve eq11 eq16738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16738
  have eq347825 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq182774 y x
       grind)
    | exact superpose eq182774 eq16
    | (have j1 := eq182774 y x
       grind)
    | exact resolve eq16 eq182774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182774
  have eq350203 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq347825
       have i₂ := eq483 y x
       grind)
    | exact superpose eq483 eq347825
    | (have j1 := eq483 y x
       grind)
    | (have r₁ := eq347825
       have r₂ := eq483 y x
       grind)
    | exact resolve eq347825 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350204 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq350203
  have eq463354 : ∀ X0 X1 X2 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op (M.op X2 X1) (M.op X1 X0)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4264 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4264
    | exact resolve eq4264 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4264
  have eq463828 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op (M.op X2 X1) (M.op X1 X0)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq463354 X0 X1 X2
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq463354
    | (have j0 := eq463354 X0 X1 X2
       grind)
    | exact resolve eq463354 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq463354
  have eq465676 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op (M.op X2 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq463828 X1 X0 X2
       grind)
    | exact superpose eq463828 eq11
    | (have j1 := eq463828 X1 X0 X2
       grind)
    | exact resolve eq11 eq463828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463828
  have eq465948 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq465676 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq465676
    | (have j0 := eq465676 X0 X1 X2
       grind)
    | exact resolve eq465676 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465676
  have eq467653 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (M.op x X0) X0
       have i₂ := eq465948 X0 X1 x
       grind)
    | exact superpose eq465948 eq21
    | (have j1 := eq465948 X0 X1 x
       grind)
    | exact resolve eq21 eq465948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq530548 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq136826 X0 X1
       grind)
    | exact superpose eq136826 eq11
    | (have j1 := eq136826 X0 X1
       grind)
    | exact resolve eq11 eq136826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136826
  have eq530838 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq530548 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq530548
    | (have j0 := eq530548 X0 X1
       grind)
    | exact resolve eq530548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530548
  have eq541941 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq530838 X0 X1
       grind)
    | (have i₁ := eq11 X0
       have i₂ := eq530838 X0 X1
       grind)
    | exact superpose eq530838 eq11
    | (have j1 := eq530838 X0 X1
       grind)
    | exact resolve eq11 eq530838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530838
  have eq542231 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq541941 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq541941
    | (have j0 := eq541941 X0 X1
       grind)
    | exact resolve eq541941 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541941
  have eq543911 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) (τ X0))
       have i₂ := eq542231 X0 X1
       grind)
    | exact superpose eq542231 eq10
    | (have j1 := eq542231 X0 X1
       grind)
    | exact resolve eq10 eq542231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542231
  have eq548562 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq543911 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq543911
    | (have j0 := eq543911 (σ X0) X1
       grind)
    | exact resolve eq543911 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543911
  have eq549043 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq548562 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq548562
    | (have j0 := eq548562 X0 X1
       grind)
    | exact resolve eq548562 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq548562
  have eq549888 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq549043 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq549043
    | (have j0 := eq549043 X1 (σ X0)
       grind)
    | exact resolve eq549043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549043
  have eq550633 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq549888 X0 X1
       have i₂ := eq4371 X0
       grind)
    | exact superpose eq4371 eq549888
    | (have j0 := eq549888 X0 X1
       grind)
    | exact resolve eq549888 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549888
  have eq550919 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq550633 X0 X1
       have i₂ := eq4625 X0
       grind)
    | exact superpose eq4625 eq550633
    | (have j0 := eq550633 X0 X1
       grind)
    | exact resolve eq550633 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550633
  have eq551134 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq550919 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq550919
    | (have j0 := eq550919 X0 X1
       grind)
    | exact resolve eq550919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550919
  have eq551297 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq551134 X0 X1
       have i₂ := eq4371 X0
       grind)
    | exact superpose eq4371 eq551134
    | (have j0 := eq551134 X0 X1
       grind)
    | exact resolve eq551134 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551134
  have eq551447 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq551297 X0 X1
       have i₂ := eq4625 X0
       grind)
    | exact superpose eq4625 eq551297
    | (have j0 := eq551297 X0 X1
       grind)
    | exact resolve eq551297 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551297
  have eq556343 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq347825
       have i₂ := eq551447 x y
       grind)
    | exact superpose eq551447 eq347825
    | (have j1 := eq551447 x y
       grind)
    | exact resolve eq347825 eq551447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551447
  have eq556346 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq556343
  have eq556347 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq556346
  have eq603856 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq173592 x (σ y)
       have i₂ := eq556347
       grind)
    | exact superpose eq556347 eq173592
    | (have j0 := eq173592 x (σ y)
       grind)
    | (have r₁ := eq173592 x (σ y)
       have r₂ := eq556347
       grind)
    | exact resolve eq173592 eq556347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173592 eq556347
  have eq603916 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq603856
  have eq603917 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq603916
  have eq603967 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq603917
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq603917
    | exact resolve eq603917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603917
  have eq603968 : (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq603967
  have eq604634 : (M.op x x) = (τ (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq603968
       grind)
    | exact superpose eq603968 eq10
    | exact resolve eq10 eq603968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603968
  have eq605550 : y = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq604634
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq604634
    | exact resolve eq604634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604634
  have eq606128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5405 x
       have i₂ := eq605550
       grind)
    | exact superpose eq605550 eq5405
    | exact resolve eq5405 eq605550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606257 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq606128
       have r₂ := eq16
       grind)
    | exact resolve eq606128 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606128
  have eq607447 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq347825
       have i₂ := eq606257
       grind)
    | exact superpose eq606257 eq347825
    | exact resolve eq347825 eq606257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347825
  have eq607456 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq483 y x
       have i₂ := eq606257
       grind)
    | exact superpose eq606257 eq483
    | (have j0 := eq483 y x
       grind)
    | exact resolve eq483 eq606257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq607480 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq34769 y x
       have i₂ := eq606257
       grind)
    | exact superpose eq606257 eq34769
    | (have j0 := eq34769 y x
       grind)
    | exact resolve eq34769 eq606257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34769
  have eq607490 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq606257
       grind)
    | exact superpose eq606257 eq10
    | exact resolve eq10 eq606257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608413 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq607490
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq607490
    | exact resolve eq607490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607490
  have eq609340 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq608413
       grind)
    | exact superpose eq608413 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq608413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626564 : x = (M.op x (M.op x y)) ∨ x = (k y x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq467653 x y
       have i₂ := eq609340
       grind)
    | exact superpose eq609340 eq467653
    | (have j0 := eq467653 x y
       grind)
    | exact resolve eq467653 eq609340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467653
  have eq626569 : x ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  have eq626572 : x = (M.op x (M.op x y)) ∨ x = (k y x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq626564
  have eq626580 : x = (M.op x x) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq626572
       have i₂ := eq608413
       grind)
    | exact superpose eq608413 eq626572
    | exact resolve eq626572 eq608413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608413 eq626572
  have eq626588 : x = (M.op x (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq626580
       have r₂ := eq626569
       grind)
    | exact resolve eq626580 eq626569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626580
  have eq667576 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq626588
       have i₂ := eq607456
       grind)
    | exact superpose eq607456 eq626588
    | exact resolve eq626588 eq607456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607456
  have eq667577 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq626588
       have i₂ := eq609340
       grind)
    | exact superpose eq609340 eq626588
    | exact resolve eq626588 eq609340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609340 eq626588
  have eq667634 : x = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq667577
  have eq667635 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq667576
  have eq667640 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq667634
       have r₂ := eq626569
       grind)
    | exact resolve eq667634 eq626569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626569 eq667634
  have eq670577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5405 x
       have i₂ := eq667635
       grind)
    | exact superpose eq667635 eq5405
    | exact resolve eq5405 eq667635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667635
  have eq670709 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq670577
       have r₂ := eq16
       grind)
    | exact resolve eq670577 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670577
  have eq670738 : x = y ∨ (σ x) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq605550
       have i₂ := eq670709
       grind)
    | exact superpose eq670709 eq605550
    | exact resolve eq605550 eq670709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605550
  have eq670933 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq670738
       have i₂ := eq606257
       grind)
    | exact superpose eq606257 eq670738
    | exact resolve eq670738 eq606257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670738
  have eq723233 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq670933
       grind)
    | exact superpose eq670933 eq16
    | exact resolve eq16 eq670933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670933
  have eq723281 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq723233
       have i₂ := eq4371 x
       grind)
    | exact superpose eq4371 eq723233
    | exact resolve eq723233 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723233
  have eq723285 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq723281
       have i₂ := eq4625 x
       grind)
    | exact superpose eq4625 eq723281
    | exact resolve eq723281 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723281
  have eq723286 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq723285
  have eq724149 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq723286
       have i₂ := eq350204
       grind)
    | exact superpose eq350204 eq723286
    | exact resolve eq723286 eq350204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350204 eq723286
  have eq724738 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq724149
  have eq725104 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq724738
       have r₂ := eq607480
       grind)
    | exact resolve eq724738 eq607480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607480 eq724738
  have eq887344 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq725104
       grind)
    | exact superpose eq725104 eq16
    | exact resolve eq16 eq725104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725104
  have eq890800 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq887344
       have i₂ := eq667640
       grind)
    | exact superpose eq667640 eq887344
    | exact resolve eq887344 eq667640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667640 eq887344
  have eq890822 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq890800
  have eq890835 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq890822
       have i₂ := eq670709
       grind)
    | exact superpose eq670709 eq890822
    | exact resolve eq890822 eq670709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670709 eq890822
  have eq890856 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq890835
  have eq901211 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq890856
       grind)
    | exact superpose eq890856 eq16
    | exact resolve eq16 eq890856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890856
  have eq901264 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq901211
       have i₂ := eq4371 x
       grind)
    | exact superpose eq4371 eq901211
    | exact resolve eq901211 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901211
  have eq901266 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq901264
       have i₂ := eq4625 x
       grind)
    | exact superpose eq4625 eq901264
    | exact resolve eq901264 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901264
  have eq901267 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq901266
  have eq901273 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq901267
       grind)
    | exact superpose eq901267 eq10
    | exact resolve eq10 eq901267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901267
  have eq902209 : x = y ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq901273
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq901273
    | exact resolve eq901273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901273
  have eq906677 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq902209
       grind)
    | exact superpose eq902209 eq16
    | exact resolve eq16 eq902209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902209
  have eq906730 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq906677
       have i₂ := eq4371 x
       grind)
    | exact superpose eq4371 eq906677
    | exact resolve eq906677 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906677
  have eq906732 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq906730
       have i₂ := eq4625 x
       grind)
    | exact superpose eq4625 eq906730
    | exact resolve eq906730 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906730
  have eq906733 : (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq906732
  have eq2088539 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq607447
       have i₂ := eq906733
       grind)
    | exact superpose eq906733 eq607447
    | (have r₁ := eq607447
       have r₂ := eq906733
       grind)
    | exact resolve eq607447 eq906733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607447
  have eq2088540 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq2088539
  have eq2088628 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2088540
       grind)
    | exact superpose eq2088540 eq16
    | exact resolve eq16 eq2088540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2088723 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq465948 (σ x) (σ y) x
       have i₂ := eq2088540
       grind)
    | exact superpose eq2088540 eq465948
    | (have j0 := eq465948 (σ x) (σ y) x
       grind)
    | exact resolve eq465948 eq2088540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465948 eq2088540
  have eq2088756 : ∀ X0 : G, (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2088723 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2088723
    | (have j0 := eq2088723 X0
       grind)
    | exact resolve eq2088723 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088723
  have eq2088826 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2088628
       have i₂ := eq906733
       grind)
    | exact superpose eq906733 eq2088628
    | exact resolve eq2088628 eq906733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906733 eq2088628
  have eq2088836 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2088756 X0
       have i₂ := eq606257
       grind)
    | exact superpose eq606257 eq2088756
    | (have j0 := eq2088756 X0
       grind)
    | exact resolve eq2088756 eq606257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606257 eq2088756
  have eq2088901 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq2088836 X0
       grind)
    | (have r₁ := eq2088836 X0
       have r₂ := eq2088826
       grind)
    | exact resolve eq2088836 eq2088826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088836
  have eq2088950 : ∀ X0 : G, (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2088901 X0
       have i₂ := eq4371 x
       grind)
    | exact superpose eq4371 eq2088901
    | (have j0 := eq2088901 X0
       grind)
    | exact resolve eq2088901 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088901
  have eq2088992 : ∀ X0 : G, (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2088950 X0
       have i₂ := eq4625 x
       grind)
    | exact superpose eq4625 eq2088950
    | (have j0 := eq2088950 X0
       grind)
    | exact resolve eq2088950 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088950
  have eq2088993 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq2088992 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088992
  have eq2092733 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2088993 (M.op x (σ x))
       have i₂ := eq2088993 x
       grind)
    | exact superpose eq2088993 eq2088993
    | exact resolve eq2088993 eq2088993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088993
  have eq2092945 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq2092733
  have eq2093041 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2092945
       have i₂ := eq4371 x
       grind)
    | exact superpose eq4371 eq2092945
    | exact resolve eq2092945 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4371 eq2092945
  have eq2093099 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2093041
       have i₂ := eq4625 x
       grind)
    | exact superpose eq4625 eq2093041
    | exact resolve eq2093041 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4625 eq2093041
  have eq2093133 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2093099
       have r₂ := eq2088826
       grind)
    | exact resolve eq2093099 eq2088826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088826 eq2093099
  have eq2097536 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2093133
       grind)
    | exact superpose eq2093133 eq10
    | exact resolve eq10 eq2093133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093133
  have eq2098714 : y = (M.op x x) := by
    first
    | (have i₁ := eq2097536
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2097536
    | exact resolve eq2097536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097536
  have eq2100179 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5405 x
       have i₂ := eq2098714
       grind)
    | exact superpose eq2098714 eq5405
    | exact resolve eq5405 eq2098714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5405 eq2098714
  have eq2100416 : False := by grind
  exact eq2100416
