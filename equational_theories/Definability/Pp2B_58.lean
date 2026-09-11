import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq80 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23 eq37
  have eq85 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq121
    | exact resolve eq121 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq122
    | exact resolve eq122 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq12504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq123 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12504
    | exact resolve eq12504 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12504
  have eq12516 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12505
       have r₂ := eq28
       grind)
    | exact resolve eq12505 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12505
  have eq12518 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12516
    | exact resolve eq12516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12516
  have eq12524 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq12518
  have eq12597 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12524
    | exact resolve eq12524 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12524
  have eq12732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12597 eq123
    | exact resolve eq123 eq12597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12597
  have eq12740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12732
  have eq12742 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12740
       have r₂ := eq28
       grind)
    | exact resolve eq12740 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12740
  have eq12753 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12742
  have eq12823 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12753
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12753
    | exact resolve eq12753 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12753
  have eq12952 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq12823
       grind)
    | exact superpose eq12823 eq80
    | exact resolve eq80 eq12823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12823
  have eq12966 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12952
    | exact resolve eq12952 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12952
  have eq12980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12966 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12983 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12980
    | exact resolve eq12980 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12980
  have eq12994 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12983
       have r₂ := eq28
       grind)
    | exact resolve eq12983 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12983
  have eq12996 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12994
    | exact resolve eq12994 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12994
  have eq12997 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12996
  have eq13003 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12997
  have eq13076 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq13003
    | exact resolve eq13003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13003
  have eq13219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13076 eq12966
    | exact resolve eq12966 eq13076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12966 eq13076
  have eq13221 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13219
  have eq13225 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13221
       have r₂ := eq28
       grind)
    | exact resolve eq13221 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13221
  have eq13227 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13225 eq28
    | exact resolve eq28 eq13225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13230 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13225 eq86
    | (have r₁ := eq86
       have r₂ := eq13225
       grind)
    | exact resolve eq86 eq13225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq13225
  have eq13237 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq13230
  have eq13949 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13237 eq123
    | exact resolve eq123 eq13237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13964 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq13949
  have eq13978 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13964
       have r₂ := eq13227
       grind)
    | exact resolve eq13964 eq13227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13964
  have eq13988 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq13978
  have eq14066 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq13988
    | exact resolve eq13988 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13988
  have eq14295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14066 eq123
    | exact resolve eq123 eq14066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq14066
  have eq14307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq14295
  have eq14311 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14307
       have r₂ := eq28
       grind)
    | exact resolve eq14307 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14307
  have eq14323 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq14311
  have eq14394 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14323
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14323
    | exact resolve eq14323 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14323
  have eq14561 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq14394
       grind)
    | exact superpose eq14394 eq80
    | exact resolve eq80 eq14394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14394
  have eq14575 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq14561
    | exact resolve eq14561 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14561
  have eq14592 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14575 eq13237
    | exact resolve eq13237 eq14575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13237
  have eq14596 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq14592
  have eq14604 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14596
       have r₂ := eq13227
       grind)
    | exact resolve eq14596 eq13227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13227 eq14596
  have eq14624 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq14604
  have eq14702 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14624
    | exact resolve eq14624 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14624
  have eq14865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14702 eq14575
    | exact resolve eq14575 eq14702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14575 eq14702
  have eq14867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14865
  have eq14875 : y = (M.op x y) := by
    first
    | (have r₁ := eq14867
       have r₂ := eq28
       grind)
    | exact resolve eq14867 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14867
  have eq14877 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq14875 eq21
    | exact resolve eq21 eq14875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq14884 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq14875 eq85
    | (have r₁ := eq85
       have r₂ := eq14875
       grind)
    | exact resolve eq85 eq14875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq14946 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq14884
  have eq14997 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14877
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14877
    | exact resolve eq14877 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14877
  have eq14999 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq14997 eq27
    | exact resolve eq27 eq14997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq16508 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq14946
       grind)
    | exact superpose eq14946 eq80
    | exact resolve eq80 eq14946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14946
  have eq16531 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14997 eq16508
    | exact resolve eq16508 eq14997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16508
  have eq16539 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16531
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16531
    | exact resolve eq16531 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16531
  have eq16545 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14997 eq16539
    | exact resolve eq16539 eq14997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16539
  have eq16555 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16545 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq16545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16556 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq16555
  have eq16558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14999 eq16556
    | exact resolve eq16556 eq14999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16556
  have eq16567 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16558
       have r₂ := eq28
       grind)
    | exact resolve eq16558 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16558
  have eq16597 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq16567
  have eq16690 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14999 eq16597
    | exact resolve eq16597 eq14999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16597
  have eq16865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16690 eq16545
    | exact resolve eq16545 eq16690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16545 eq16690
  have eq16867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq16865
  have eq16869 : y = (M.op x x) := by
    first
    | (have r₁ := eq16867
       have r₂ := eq28
       grind)
    | exact resolve eq16867 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16867
  have eq16893 : (M.op x y) = (k y x) := by grind
  clear eq16869
  have eq16987 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16893
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16893
    | exact resolve eq16893 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16893
  have eq17001 : y = (k y x) := by
    first
    | exact superpose eq14875 eq16987
    | exact resolve eq16987 eq14875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14875 eq16987
  have eq17129 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq17001
       grind)
    | exact superpose eq17001 eq80
    | exact resolve eq80 eq17001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq17001
  have eq17151 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq14997 eq17129
    | exact resolve eq17129 eq14997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17129
  have eq17158 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq17151
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17151
    | exact resolve eq17151 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17151
  have eq17164 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq14997 eq17158
    | exact resolve eq17158 eq14997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14997 eq17158
  have eq17217 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17164 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq17164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17218 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq17217
  have eq17220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14999 eq17218
    | exact resolve eq17218 eq14999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17218
  have eq17229 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq17220
       have r₂ := eq28
       grind)
    | exact resolve eq17220 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17220
  have eq17393 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq17229
  have eq17484 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq14999 eq17393
    | exact resolve eq17393 eq14999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14999 eq17393
  have eq17500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17164 eq17484
    | exact resolve eq17484 eq17164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17164 eq17484
  have eq17504 : False := by grind
  exact eq17504

/-- `Equation3735`: `x ◇ y = (x ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxx_pxx_pyx_Equation3735 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3735 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3735.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X0)) := by
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
  have eq50 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X2) X3 (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op y x) = (M.op (M.op y X0) (M.op x y)) := by
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
  have eq54 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op (M.op X1 X0) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X0 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X1 X0) (M.op X0 X2)
       grind)
    | (have r₁ := eq13 (M.op X1 X0) (M.op X0 X1)
       have r₂ := eq14 X0 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X1 (M.op X0 X0)
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq113
    | (have j0 := eq113 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq113 X0 (M.op X1 X1)
       have r₂ := eq14 X1 X1 X1
       grind)
    | exact resolve eq113 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq123 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq209 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq213 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k X0 (M.op X1 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X2 X0
       have i₂ := eq124 X1 X0
       grind)
    | exact superpose eq124 eq14
    | exact resolve eq14 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq124 X1 (τ X0)
       grind)
    | exact superpose eq124 eq34
    | exact resolve eq34 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq294 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) y) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq11 y (τ X0)
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 (τ X0) (τ X0)
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq340 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq11 X1 (τ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (τ X0) (τ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq437 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq251
    | (have j0 := eq251 X0 (M.op x y)
       grind)
    | exact resolve eq251 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq497 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (k X0 (M.op X1 X1)) (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X0 X2 X3
       have i₂ := eq124 X1 X0
       grind)
    | exact superpose eq124 eq52
    | exact resolve eq52 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X1 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X3 X0 (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq519 X0 x
       have i₂ := eq14 X0 sF2 x
       grind)
    | exact superpose eq14 eq519
    | exact resolve eq519 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq530 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq516 X0 X1 X2 x
       have i₂ := eq14 X1 X0 x
       grind)
    | exact superpose eq14 eq516
    | exact resolve eq516 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq533 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq527 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (M.op X0 (σ x))
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op X0 (σ x))
       have r₂ := eq527 X0
       grind)
    | exact resolve eq13 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq536 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq533 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq616 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) = (M.op (M.op X1 X4) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 X4 X0 (M.op (M.op X0 X1) X3)
       have i₂ := eq55 X1 X0 X2 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq622 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq616 X0 X1 X2 X3 x
       have i₂ := eq52 X1 x X2 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq616
    | exact resolve eq616 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq641 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq622 X0 X1 x X3
       have i₂ := eq14 X1 X0 x
       grind)
    | exact superpose eq14 eq622
    | exact resolve eq622 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq723 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq765 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq213 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq213
    | (have j0 := eq213 y X0
       grind)
    | exact resolve eq213 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq766 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X0)) = (M.op (M.op x X1) (M.op y x)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq213
    | exact resolve eq213 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq784 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq766 X0 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq766
    | exact resolve eq766 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq785 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq784 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq784
    | (have j0 := eq784 X0
       grind)
    | exact resolve eq784 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq825 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq113
    | (have j0 := eq113 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq113 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq113 X0 (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | exact resolve eq113 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq839 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq825 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq844 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq839 X0 X1
       have j1 := eq113 X1 (σ X0)
       grind)
    | (have r₁ := eq839 X0 X1
       have r₂ := eq113 X0 (σ X0)
       grind)
    | exact resolve eq839 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq839
  have eq882 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq785 eq765
    | exact resolve eq765 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq898 : (M.op x y) ≠ (M.op x y) ∨ (M.op y y) = (k y (M.op x y)) := by
    first
    | exact superpose eq882 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq882
       grind)
    | exact resolve eq13 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq907 : (M.op y y) = (k y (M.op x y)) := by grind
  clear eq898
  have eq912 : (k (σ y) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq907 eq76
    | exact resolve eq76 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq216
    | (have j0 := eq216 (σ y) X0
       grind)
    | exact resolve eq216 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) X1) (M.op (σ y) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq216
    | exact resolve eq216 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq941 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq216 eq124
    | exact resolve eq124 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq937 X0 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq937
    | exact resolve eq937 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq956 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq955
    | (have j0 := eq955 X0
       grind)
    | exact resolve eq955 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1069 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq956 eq936
    | exact resolve eq936 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq956
  have eq1086 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1069 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq1069
       grind)
    | exact resolve eq13 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1069 eq14
    | exact resolve eq14 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1095 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq1086
  have eq1097 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq1088
    | exact resolve eq1088 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1088
  have eq1622 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq530 X2 X0 (M.op X0 X1)
       have i₂ := eq52 X0 X2 X1 X2
       grind)
    | exact superpose eq52 eq530
    | exact resolve eq530 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1625 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq213 eq530
    | exact resolve eq530 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1627 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq216 eq530
    | exact resolve eq530 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq1719 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq1625 eq50
    | exact resolve eq50 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1737 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq1719
    | exact resolve eq1719 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq1798 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1627 eq51
    | exact resolve eq51 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1806 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq1798
    | exact resolve eq1798 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1798
  have eq2317 : ∀ X0 X1 : G, (σ (k X0 (M.op X1 X1))) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 (M.op X1 X1)
       have i₂ := eq248 (σ X0) X1
       grind)
    | exact superpose eq248 eq10
    | exact resolve eq10 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2348 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2317 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq2317
    | exact resolve eq2317 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317
  have eq3215 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq641 X0 X1 X3
       have i₂ := eq1622 X1 X0 (M.op (M.op X0 X1) X3)
       grind)
    | exact superpose eq1622 eq641
    | exact resolve eq641 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq3216 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3215 X0 X1 X3
       have i₂ := eq1622 X0 X1 X3
       grind)
    | exact superpose eq1622 eq3215
    | exact resolve eq3215 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3215
  have eq3221 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3216 X0 X2 X0
       have i₂ := eq124 X1 X0
       grind)
    | exact superpose eq124 eq3216
    | exact resolve eq3216 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3295 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 X2 (M.op X0 X1)
       have i₂ := eq3216 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq3216 eq124
    | exact resolve eq124 eq3216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3392 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X0 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3295 X0 X1 X2
       have i₂ := eq1622 X0 X1 X0
       grind)
    | exact superpose eq1622 eq3295
    | exact resolve eq3295 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295
  have eq5091 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq723 X0 X1
       have i₂ := eq1622 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1622 eq723
    | exact resolve eq723 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq5092 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5091 X0 X1
       have i₂ := eq3216 X0 X0 X1
       grind)
    | exact superpose eq3216 eq5091
    | exact resolve eq5091 eq3216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5091
  have eq5628 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq844 (M.op X0 X0) X1
       have i₂ := eq5092 X0 X0
       grind)
    | exact superpose eq5092 eq844
    | (have j0 := eq844 (M.op X0 X0) X1
       grind)
    | exact resolve eq844 eq5092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5092
  have eq5644 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5628 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5628
  have eq5831 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5644 x X0
       have i₂ := eq248 X0 x
       grind)
    | exact superpose eq248 eq5644
    | exact resolve eq5644 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq5899 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (k x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (M.op X0 X0)
       have i₂ := eq5644 X0 sF2
       grind)
    | exact superpose eq5644 eq35
    | exact resolve eq35 eq5644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq5900 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (k y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq5644 X0 sF3
       grind)
    | exact superpose eq5644 eq36
    | exact resolve eq36 eq5644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq5644
  have eq5927 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5900 x
       have i₂ := eq2348 y x
       grind)
    | exact superpose eq2348 eq5900
    | exact resolve eq5900 eq2348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5900
  have eq5928 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5899 x
       have i₂ := eq2348 x x
       grind)
    | exact superpose eq2348 eq5899
    | exact resolve eq5899 eq2348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5899
  have eq5988 : (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5927
       have i₂ := eq912
       grind)
    | exact superpose eq912 eq5927
    | exact resolve eq5927 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912 eq5927
  have eq6022 : (k y (M.op x y)) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5988 eq112
    | exact resolve eq112 eq5988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq6024 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq907 eq6022
    | exact resolve eq6022 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq6022
  have eq6027 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (k X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq497 X0 X1 X2 X3
       have i₂ := eq3216 X3 (k X0 (M.op X1 X1)) (M.op X0 X2)
       grind)
    | exact superpose eq3216 eq497
    | exact resolve eq497 eq3216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq6028 : ∀ X0 X1 X3 : G, (M.op X0 X3) = (M.op (k X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6027 X0 X1 x X3
       have i₂ := eq1622 X0 x X3
       grind)
    | exact superpose eq1622 eq6027
    | exact resolve eq6027 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6027
  have eq6033 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq5928
       grind)
    | exact superpose eq5928 eq16
    | exact resolve eq16 eq5928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6036 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq37 (M.op x x)
       have i₂ := eq5928
       grind)
    | exact superpose eq5928 eq37
    | exact resolve eq37 eq5928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq6053 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq6036
       have i₂ := eq124 sF2 sF1
       grind)
    | exact superpose eq124 eq6036
    | exact resolve eq6036 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6036
  have eq6057 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq6053
       have i₂ := eq2348 sF0 x
       grind)
    | exact superpose eq2348 eq6053
    | exact resolve eq6053 eq2348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348 eq6053
  have eq6060 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq1625 eq6057
    | exact resolve eq6057 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6057
  have eq6062 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1737 eq6060
    | exact resolve eq6060 eq1737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737 eq6060
  have eq6063 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6062
       have i₂ := eq5928
       grind)
    | exact superpose eq5928 eq6062
    | exact resolve eq6062 eq5928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6062
  have eq6098 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq6063 eq1622
    | exact resolve eq1622 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6101 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq6063 eq3216
    | exact resolve eq3216 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6104 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq6101 x
       have i₂ := eq3216 sF1 x sF1
       grind)
    | exact superpose eq3216 eq6101
    | exact resolve eq6101 eq3216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6101
  have eq6107 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq6098 x
       have i₂ := eq1622 sF1 sF1 x
       grind)
    | exact superpose eq1622 eq6098
    | exact resolve eq6098 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6098
  have eq6368 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq6104 eq536
    | exact resolve eq536 eq6104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq6460 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1627 eq6368
    | exact resolve eq6368 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6368
  have eq6472 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1806 eq6460
    | exact resolve eq6460 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6460
  have eq6476 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq6063 eq6472
    | exact resolve eq6472 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6472
  have eq6540 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq6107
    | (have j0 := eq6107 (σ y)
       grind)
    | exact resolve eq6107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6107
  have eq7100 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6063 eq6033
    | exact resolve eq6033 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6033
  have eq7594 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5831 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq5831
    | exact resolve eq5831 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7624 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq5831 X0
       grind)
    | exact superpose eq5831 eq16
    | exact resolve eq16 eq5831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5831
  have eq10000 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq209 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq209
    | (have j0 := eq209 y
       grind)
    | exact resolve eq209 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq209
  have eq10045 : (M.op (σ x) (σ y)) = (σ (k y (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq6540 eq10000
    | exact resolve eq10000 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10000
  have eq10070 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq76 eq10045
    | exact resolve eq10045 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq10045
  have eq10088 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq5988 eq10070
    | exact resolve eq10070 eq5988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5988 eq10070
  have eq10099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6540 eq10088
    | exact resolve eq10088 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10088
  have eq10107 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq10099
       have r₂ := eq27
       grind)
    | exact resolve eq10099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10099
  have eq10157 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k (σ y) (M.op X0 X0)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq10107 eq231
    | exact resolve eq231 eq10107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq10107
  have eq10177 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10157 x
       have i₂ := eq6028 sF3 x sF4
       grind)
    | exact superpose eq6028 eq10157
    | exact resolve eq10157 eq6028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6028 eq10157
  have eq10202 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1097 eq10177
    | exact resolve eq10177 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq10177
  have eq10221 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6104 eq10202
    | exact resolve eq10202 eq6104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6104 eq10202
  have eq10403 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq10221 eq3392
    | exact resolve eq3392 eq10221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392 eq10221
  have eq10410 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10403 x
       have i₂ := eq124 x sF4
       grind)
    | exact superpose eq124 eq10403
    | exact resolve eq10403 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10403
  have eq10432 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1627 eq10410
    | exact resolve eq10410 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10410
  have eq10453 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1806 eq10432
    | exact resolve eq10432 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10432
  have eq10469 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6063 eq10453
    | exact resolve eq10453 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10453
  have eq12261 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10469 eq6024
    | exact resolve eq6024 eq10469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6024 eq10469
  have eq12339 : (M.op y y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7100 eq12261
    | exact resolve eq12261 eq7100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12261
  have eq12378 : (M.op x y) = (M.op (M.op x y) (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq785 y
       have i₂ := eq12339
       grind)
    | exact superpose eq12339 eq785
    | exact resolve eq785 eq12339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq12339
  have eq12442 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq50 eq12378
    | exact resolve eq12378 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq12378
  have eq12477 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq12442 eq7100
    | exact resolve eq7100 eq12442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12442
  have eq12538 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq30 eq12477
    | exact resolve eq12477 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12477
  have eq12539 : (M.op x y) = (M.op x x) := by grind
  clear eq12538
  have eq12544 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5928
       have i₂ := eq12539
       grind)
    | exact superpose eq12539 eq5928
    | exact resolve eq5928 eq12539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12555 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq124 x X0
       have i₂ := eq12539
       grind)
    | exact superpose eq12539 eq124
    | exact resolve eq124 eq12539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq12567 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (k X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq3221 X1 x X0
       have i₂ := eq12539
       grind)
    | exact superpose eq12539 eq3221
    | exact resolve eq3221 eq12539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221
  have eq12575 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq12539
       grind)
    | exact superpose eq12539 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq12539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12621 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6063 eq12544
    | exact resolve eq12544 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12544
  have eq12637 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq12621
    | exact resolve eq12621 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12621
  have eq12649 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12637 eq6476
    | exact resolve eq6476 eq12637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6476
  have eq12768 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq941 X0
       have i₂ := eq12555 X0
       grind)
    | exact superpose eq12555 eq941
    | exact resolve eq941 eq12555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq12876 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq1627 eq12768
    | exact resolve eq12768 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12768
  have eq12919 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq6063 eq12876
    | exact resolve eq12876 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12876
  have eq12937 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq12637 eq12919
    | exact resolve eq12919 eq12637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12919
  have eq15497 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq7594 X0
       grind)
    | exact superpose eq7594 eq79
    | (have j0 := eq79 X0
       grind)
    | exact resolve eq79 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq7594
  have eq15792 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15497 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15497
    | (have j0 := eq15497 x
       grind)
    | exact resolve eq15497 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15497
  have eq15837 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15792
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq15792
    | exact resolve eq15792 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15792
  have eq15885 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15837
    | exact resolve eq15837 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15837
  have eq15921 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15885
       have i₂ := eq5928
       grind)
    | exact superpose eq5928 eq15885
    | exact resolve eq15885 eq5928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15885
  have eq15954 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6063 eq15921
    | exact resolve eq15921 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15921
  have eq15975 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12637 eq15954
    | exact resolve eq15954 eq12637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15954
  have eq15993 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15975
    | exact resolve eq15975 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15975
  have eq17037 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (k X0 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq437 eq12567
    | exact resolve eq12567 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12567
  have eq17209 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (k X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq12937 eq17037
    | exact resolve eq17037 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12937 eq17037
  have eq18344 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq340 X0 X1
       have i₂ := eq7624 X0
       grind)
    | exact superpose eq7624 eq340
    | (have j0 := eq340 X0 X1
       grind)
    | exact resolve eq340 eq7624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq18657 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq28 eq18344
    | exact resolve eq18344 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18344
  have eq18781 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq39 eq18657
    | (have j0 := eq18657 X0
       grind)
    | exact resolve eq18657 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq18657
  have eq18839 : ∀ X0 : G, x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (k X0 x)) = (σ (M.op x X0)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq6063 eq18781
    | (have j0 := eq18781 X0
       grind)
    | exact resolve eq18781 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18781
  have eq18873 : ∀ X0 : G, x = (M.op x x) ∨ (σ (k X0 x)) = (σ (M.op x X0)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq7100 eq18839
    | (have j0 := eq18839 X0
       grind)
    | exact resolve eq18839 eq7100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18839
  have eq18898 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ x = (M.op x y) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq18873 X0
       have i₂ := eq12539
       grind)
    | exact superpose eq12539 eq18873
    | (have j0 := eq18873 X0
       grind)
    | exact resolve eq18873 eq12539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18873
  have eq32077 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq18898 x
       grind)
    | exact superpose eq18898 eq43
    | (have j1 := eq18898 y
       grind)
    | exact resolve eq43 eq18898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq32078 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18898 y
       grind)
    | exact superpose eq18898 eq74
    | (have j1 := eq18898 y
       grind)
    | exact resolve eq74 eq18898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq18898
  have eq32156 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32078
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32078
    | exact resolve eq32078 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32078
  have eq32157 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32077
       have i₂ := eq5928
       grind)
    | exact superpose eq5928 eq32077
    | exact resolve eq32077 eq5928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5928 eq32077
  have eq32182 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq32156
    | exact resolve eq32156 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32156
  have eq32183 : (k (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6063 eq32157
    | exact resolve eq32157 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32157
  have eq32205 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32182
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32182
    | exact resolve eq32182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32182
  have eq32206 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32205
  have eq32207 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq12637 eq32183
    | exact resolve eq32183 eq12637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12637 eq32183
  have eq32229 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32207
       have i₂ := eq12539
       grind)
    | exact superpose eq12539 eq32207
    | exact resolve eq32207 eq12539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32207
  have eq32230 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32229
  have eq32307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32206 eq15993
    | exact resolve eq15993 eq32206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15993
  have eq32320 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq32307
       have r₂ := eq27
       grind)
    | exact resolve eq32307 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32307
  have eq32337 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32230 eq49
    | exact resolve eq49 eq32230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq32230
  have eq32362 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq32337
    | exact resolve eq32337 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32337
  have eq32372 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq32362
       have r₂ := eq12575
       grind)
    | exact resolve eq32362 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12575 eq32362
  have eq32395 : ∀ X0 : G, (σ x) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq844 x X0
       have i₂ := eq32372
       grind)
    | exact superpose eq32372 eq844
    | (have j0 := eq844 x X0
       grind)
    | exact resolve eq844 eq32372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq32372
  have eq32411 : ∀ X0 : G, (σ x) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq20 eq32395
    | (have j0 := eq32395 X0
       grind)
    | exact resolve eq32395 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32395
  have eq32422 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq32411 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32411
    | (have j0 := eq32411 X0
       grind)
    | exact resolve eq32411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32411
  have eq32427 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq32422 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32422
    | (have j0 := eq32422 X0
       grind)
    | exact resolve eq32422 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32422
  have eq32945 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32320 eq1095
    | exact resolve eq1095 eq32320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32320
  have eq78076 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq12555 eq17209
    | exact resolve eq17209 eq12555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17209
  have eq126093 : ∀ X0 : G, (M.op X0 (τ (M.op (σ x) (σ y)))) = (M.op X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1627 eq78076
    | exact resolve eq78076 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126483 : ∀ X0 : G, (M.op X0 (τ (M.op (σ x) (σ y)))) = (M.op X0 (τ (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | exact superpose eq1806 eq126093
    | exact resolve eq126093 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126093
  have eq126633 : ∀ X0 : G, (M.op X0 (τ (M.op (σ x) (σ y)))) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq126483 x
       have i₂ := eq78076 sF2 x
       grind)
    | exact superpose eq78076 eq126483
    | exact resolve eq126483 eq78076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78076 eq126483
  have eq126742 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq28 eq126633
    | exact resolve eq126633 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq126633
  have eq126893 : (M.op (τ (M.op (σ x) (σ y))) x) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq126742 eq12555
    | exact resolve eq12555 eq126742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12555 eq126742
  have eq127096 : (M.op (τ (M.op (σ x) (σ y))) x) = (τ (k (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq437 eq126893
    | exact resolve eq126893 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq126893
  have eq127166 : (τ (σ (M.op x y))) = (M.op (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq12649 eq127096
    | exact resolve eq127096 eq12649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12649 eq127096
  have eq127201 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq30 eq127166
    | exact resolve eq127166 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq127166
  have eq127276 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (τ (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq127201 eq1622
    | exact resolve eq1622 eq127201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622 eq127201
  have eq127308 : ∀ X0 : G, (M.op x X0) = (M.op (τ (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq1625 eq127276
    | exact resolve eq127276 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625 eq127276
  have eq897995 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq32427 (σ y)
       grind)
    | (have r₁ := eq32945
       have r₂ := eq32427 x
       grind)
    | exact resolve eq32945 eq32427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32427 eq32945
  have eq898010 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq897995 eq32206
    | exact resolve eq32206 eq897995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32206 eq897995
  have eq898101 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq898010
  have eq901633 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq898101 eq530
    | exact resolve eq530 eq898101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898101
  have eq901679 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq901633 x
       have i₂ := eq3216 sF3 sF1 x
       grind)
    | exact superpose eq3216 eq901633
    | exact resolve eq901633 eq3216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901633
  have eq901752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6540 eq901679
    | exact resolve eq901679 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901679
  have eq901788 : x = (M.op x y) := by
    first
    | (have r₁ := eq901752
       have r₂ := eq27
       grind)
    | exact resolve eq901752 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901752
  have eq901818 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq901788 eq20
    | exact resolve eq20 eq901788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902175 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq901818
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq901818
    | exact resolve eq901818 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901818
  have eq1476139 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) y) := by
    intro X0
    first
    | (have i₁ := eq294 X0
       have i₂ := eq7624 X0
       grind)
    | exact superpose eq7624 eq294
    | (have j0 := eq294 X0
       grind)
    | exact resolve eq294 eq7624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq7624
  have eq1480662 : (σ (M.op x y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq127308 eq1476139
    | (have j0 := eq1476139 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1476139 eq127308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127308 eq1476139
  have eq1481142 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (τ (M.op (σ x) (σ y))) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1095 eq1480662
    | exact resolve eq1480662 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095 eq1480662
  have eq1481317 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (τ (M.op (σ x) (σ y))) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1481142
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1481142
    | exact resolve eq1481142 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481142
  have eq1481464 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (τ (M.op (σ x) (σ y))) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq1481317
    | exact resolve eq1481317 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1481317
  have eq1481591 : (τ (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1627 eq1481464
    | exact resolve eq1481464 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627 eq1481464
  have eq1481706 : (τ (M.op (σ x) (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1806 eq1481591
    | exact resolve eq1481591 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806 eq1481591
  have eq1481808 : (τ (M.op (σ x) (σ y))) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6063 eq1481706
    | exact resolve eq1481706 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6063 eq1481706
  have eq1481880 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7100 eq1481808
    | exact resolve eq1481808 eq7100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7100 eq1481808
  have eq1481912 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1481880
       have i₂ := eq12539
       grind)
    | exact superpose eq12539 eq1481880
    | exact resolve eq1481880 eq12539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12539 eq1481880
  have eq1481939 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq901788 eq1481912
    | exact resolve eq1481912 eq901788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481912
  have eq1481960 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1481939
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1481939
    | exact resolve eq1481939 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1481939
  have eq1481977 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq901788 eq1481960
    | exact resolve eq1481960 eq901788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901788 eq1481960
  have eq1481978 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1481977
  have eq1482128 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1481978 eq530
    | exact resolve eq530 eq1481978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq1481978
  have eq1482181 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1482128 x
       have i₂ := eq3216 sF3 sF1 x
       grind)
    | exact superpose eq3216 eq1482128
    | exact resolve eq1482128 eq3216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3216 eq1482128
  have eq1482266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6540 eq1482181
    | exact resolve eq1482181 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6540 eq1482181
  have eq1482311 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1482266
       have r₂ := eq27
       grind)
    | exact resolve eq1482266 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482266
  have eq1482365 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1482311 eq15
    | exact resolve eq15 eq1482311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482311
  have eq1483219 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1482365
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1482365
    | exact resolve eq1482365 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1482365
  have eq1483507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq902175 eq1483219
    | exact resolve eq1483219 eq902175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902175 eq1483219
  have eq1483726 : False := by grind
  exact eq1483726

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation3868 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3868 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq43 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq43 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq48 X0 X1
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq51 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq51
  have eq62 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq20 X1
       grind)
    | exact superpose eq20 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq55
  have eq117 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq121 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       have j1 := eq62 X1 X0
       grind)
    | (have r₁ := eq117 X1 X0
       have r₂ := eq62 X0 X1
       grind)
    | (have r₁ := eq117 X1 X1
       have r₂ := eq62 X1 X1
       grind)
    | exact resolve eq117 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq117
  have eq362 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq121 (σ X1) (σ X0)
       grind)
    | exact superpose eq121 eq15
    | exact resolve eq15 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq362 X0 X1
       have i₂ := eq121 X1 X0
       grind)
    | exact superpose eq121 eq362
    | exact resolve eq362 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq362
  have eq372 : False := by grind
  exact eq372

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3868 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3868 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
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
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq113 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq592
    | exact resolve eq592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq596 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq593
       have r₂ := eq27
       grind)
    | exact resolve eq593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq598 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq596
    | exact resolve eq596 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq598
    | exact resolve eq598 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq605 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq600 eq51
    | (have r₁ := eq51
       have r₂ := eq600
       grind)
    | exact resolve eq51 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq608 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq605
  have eq618 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq608 eq81
    | exact resolve eq81 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq626 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq618
    | exact resolve eq618 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq618
  have eq630 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq626
       have r₂ := eq50
       grind)
    | exact resolve eq626 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq633 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq630
       grind)
    | exact superpose eq630 eq74
    | exact resolve eq74 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq630
       grind)
    | exact superpose eq630 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq635 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq634
  have eq637 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq635
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq635
    | exact resolve eq635 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq638 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq637
  have eq639 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq633
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq633
    | exact resolve eq633 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq642 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq638
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq638
    | exact resolve eq638 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq711 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq642 eq67
    | (have r₁ := eq67
       have r₂ := eq642
       grind)
    | exact resolve eq67 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq713 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq642 eq51
    | exact resolve eq51 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq642 eq27
    | exact resolve eq27 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq715 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq711
  have eq721 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq639 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq722 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq721
  have eq726 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq722
    | exact resolve eq722 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq727 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq726
  have eq732 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq727
    | exact resolve eq727 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq734 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq732 eq27
    | exact resolve eq27 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq762 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq715 eq81
    | exact resolve eq81 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq715
  have eq773 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq762
    | exact resolve eq762 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq762
  have eq778 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq773
       have r₂ := eq66
       grind)
    | exact resolve eq773 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq786 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq778
       grind)
    | exact superpose eq778 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq787 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq786
  have eq789 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq787
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq787
    | exact resolve eq787 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq790 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq789
  have eq795 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq790
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq790
    | exact resolve eq790 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq790
  have eq804 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq795 eq100
    | exact resolve eq100 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq813 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq795 eq713
    | (have r₁ := eq713
       have r₂ := eq795
       grind)
    | exact resolve eq713 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq795
  have eq819 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq813
  have eq820 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq819
  have eq826 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq804
  have eq954 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq826 eq820
    | exact resolve eq820 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq826
  have eq958 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq954
  have eq962 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq958
       have r₂ := eq714
       grind)
    | exact resolve eq958 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq958
  have eq964 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq962 eq20
    | exact resolve eq20 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq966 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq962 eq50
    | (have r₁ := eq50
       have r₂ := eq962
       grind)
    | exact resolve eq50 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq977 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq966
  have eq986 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq964
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq964
    | exact resolve eq964 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1030 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq986 eq26
    | exact resolve eq26 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq986 eq734
    | (have r₁ := eq734
       have r₂ := eq986
       grind)
    | exact resolve eq734 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1055 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1049
  have eq1056 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1055
  have eq1118 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1056 eq27
    | exact resolve eq27 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1129 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq74
    | exact resolve eq74 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1135 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1129
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1129
    | exact resolve eq1129 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1190 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1030 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1030
       grind)
    | exact resolve eq12 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1190
       have r₂ := eq1056
       grind)
    | exact resolve eq1190 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq1190
  have eq1194 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1193
       have r₂ := eq27
       grind)
    | exact resolve eq1193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1195 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq986 eq1135
    | exact resolve eq1135 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq1135
  have eq1217 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1195
  have eq1277 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1217 eq1194
    | exact resolve eq1194 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq1217
  have eq1281 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1277
  have eq1285 : x = (M.op x y) := by
    first
    | (have r₁ := eq1281
       have r₂ := eq1118
       grind)
    | exact resolve eq1281 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118 eq1281
  have eq1289 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1285 eq20
    | exact resolve eq20 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1291 : x ≠ y ∨ x = (k y x) := by
    first
    | exact superpose eq1285 eq50
    | exact resolve eq50 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1293 : x ≠ x ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq1285 eq66
    | (have r₁ := eq66
       have r₂ := eq1285
       grind)
    | exact resolve eq66 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1303 : y = (k y x) ∨ x = y := by grind
  clear eq1293
  have eq1314 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1289
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1289
    | exact resolve eq1289 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1369 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1314 eq26
    | exact resolve eq26 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1556 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq1303
       grind)
    | exact superpose eq1303 eq74
    | exact resolve eq74 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1303
  have eq1565 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1314 eq1556
    | exact resolve eq1556 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1569 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq1565
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1565
    | exact resolve eq1565 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1579 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1569 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1580 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq1579
  have eq1583 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1369 eq1580
    | exact resolve eq1580 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1580
  have eq1586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1369 eq1583
    | exact resolve eq1583 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1589 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1586
       have r₂ := eq27
       grind)
    | exact resolve eq1586 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1594 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq1589 eq27
    | exact resolve eq27 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1595 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq1589 eq51
    | (have r₁ := eq51
       have r₂ := eq1589
       grind)
    | exact resolve eq51 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1589
  have eq1602 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq1595
  have eq1606 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1314 eq1602
    | exact resolve eq1602 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1629 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1606 eq1569
    | exact resolve eq1569 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1630 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1606 eq113
    | exact resolve eq113 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq1606
  have eq1633 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1629
  have eq1638 : (τ (σ (M.op x y))) = (k y x) ∨ x = y := by
    first
    | exact superpose eq1285 eq1630
    | exact resolve eq1630 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq1639 : x = y := by
    first
    | (have r₁ := eq1633
       have r₂ := eq1594
       grind)
    | exact resolve eq1633 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594 eq1633
  have eq1643 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq1638
    | exact resolve eq1638 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1638
  have eq1646 : x = (k y x) ∨ x = y := by
    first
    | exact superpose eq1285 eq1643
    | exact resolve eq1643 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285 eq1643
  have eq1648 : x = (k y x) := by
    first
    | (have r₁ := eq1646
       have r₂ := eq1291
       grind)
    | exact resolve eq1646 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq1646
  have eq1650 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1639
       grind)
    | exact superpose eq1639 eq24
    | exact resolve eq24 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1686 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1650
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1650
    | exact resolve eq1650 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq1698 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1314 eq1686
    | exact resolve eq1686 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq1809 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1698 eq1369
    | exact resolve eq1369 eq1698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369 eq1698
  have eq1837 : x = (k x x) := by
    first
    | (have i₁ := eq1648
       have i₂ := eq1639
       grind)
    | exact superpose eq1639 eq1648
    | exact resolve eq1648 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639 eq1648
  have eq1839 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq43
    | exact resolve eq43 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1837
  have eq1843 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1314 eq1839
    | exact resolve eq1839 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839
  have eq1844 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1843
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1843
    | exact resolve eq1843 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1843
  have eq1845 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1314 eq1844
    | exact resolve eq1844 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314 eq1844
  have eq1859 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1845 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq1860 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1859
  have eq2096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1809 eq1860
    | exact resolve eq1860 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809 eq1860
  have eq2097 : False := by grind
  exact eq2097

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation3868 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3868 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X1 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq100 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = X0 := by
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
  clear eq19
  have eq109 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  have eq111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X1)) ∨ (k (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X1 X1))
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X1 X1))
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq111 X0 X0
       grind)
    | (have r₁ := eq110 x
       have r₂ := eq111 x x
       grind)
    | exact resolve eq110 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq111
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq116
    | exact resolve eq116 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq377 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (M.op X0 X0) X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 X0)
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq62
    | (have j1 := eq109 X0
       grind)
    | exact resolve eq62 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq109
  have eq897 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq377 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq377
    | (have j0 := eq377 X0
       have j1 := eq65 X0
       grind)
    | exact resolve eq377 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq377
  have eq901 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq897 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq911 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq901 X0
       grind)
    | exact superpose eq901 eq117
    | (have j1 := eq901 X0
       grind)
    | exact resolve eq117 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq901
  have eq915 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq911 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq933 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq915 (σ X0)
       grind)
    | exact superpose eq915 eq15
    | exact resolve eq15 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq952 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq933 X0
       have i₂ := eq915 X0
       grind)
    | exact superpose eq915 eq933
    | exact resolve eq933 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq933
  have eq2427 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq16
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq2768 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq2831 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2768 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2768
    | (have j0 := eq2768 X0 X1
       grind)
    | exact resolve eq2768 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq14257 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2427
       have i₂ := eq2831 y x
       grind)
    | exact superpose eq2831 eq2427
    | (have j1 := eq2831 (σ x) (σ y)
       grind)
    | (have r₁ := eq2427
       have r₂ := eq2831 y x
       grind)
    | (have r₁ := eq2427
       have r₂ := eq2831 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2427
       have r₂ := eq2831 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2427 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14258 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq14257
  have eq14260 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14258
       grind)
    | exact superpose eq14258 eq16
    | exact resolve eq16 eq14258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14258
  have eq14261 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq14260
       have r₂ := eq952 x
       grind)
    | exact resolve eq14260 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14260
  have eq14263 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14261
       grind)
    | exact superpose eq14261 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14261
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14261
       grind)
    | exact resolve eq12 eq14261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14261
  have eq14266 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq14263
  have eq14267 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2427
       have i₂ := eq14266
       grind)
    | exact superpose eq14266 eq2427
    | exact resolve eq2427 eq14266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427 eq14266
  have eq14268 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq14267
  have eq14269 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq14268
  have eq14275 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq14269
       grind)
    | exact superpose eq14269 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14269
       grind)
    | exact resolve eq12 eq14269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14269
  have eq14278 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq14275
  have eq14283 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14278
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq14278
    | exact resolve eq14278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14278
  have eq14298 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14283
       grind)
    | exact superpose eq14283 eq16
    | exact resolve eq16 eq14283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14283
  have eq14357 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14298
       have i₂ := eq2831 y x
       grind)
    | exact superpose eq2831 eq14298
    | (have j1 := eq2831 (σ x) (σ y)
       grind)
    | (have r₁ := eq14298
       have r₂ := eq2831 y x
       grind)
    | (have r₁ := eq14298
       have r₂ := eq2831 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq14298
       have r₂ := eq2831 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq14298 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831
  have eq14358 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq14357
  have eq14362 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14358
       grind)
    | exact superpose eq14358 eq16
    | exact resolve eq16 eq14358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14358
  have eq14363 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14362
       have r₂ := eq952 x
       grind)
    | exact resolve eq14362 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14362
  have eq14365 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14363
       grind)
    | exact superpose eq14363 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14363
       grind)
    | exact resolve eq12 eq14363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14363
  have eq14368 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq14365
  have eq14369 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14298
       have i₂ := eq14368
       grind)
    | exact superpose eq14368 eq14298
    | exact resolve eq14298 eq14368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14298 eq14368
  have eq14373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq14369
  have eq14374 : (σ x) = (σ y) := by grind
  clear eq14373
  have eq14375 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14374
       grind)
    | exact superpose eq14374 eq16
    | exact resolve eq16 eq14374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14376 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14374
       grind)
    | exact superpose eq14374 eq10
    | exact resolve eq10 eq14374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14374
  have eq14437 : x = y := by
    first
    | (have i₁ := eq14376
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14376
    | exact resolve eq14376 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14376
  have eq14438 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14375
       have i₂ := eq952 x
       grind)
    | exact superpose eq952 eq14375
    | exact resolve eq14375 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq14375
  have eq14443 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14438
       have i₂ := eq14437
       grind)
    | exact superpose eq14437 eq14438
    | exact resolve eq14438 eq14437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14437 eq14438
  have eq14444 : False := by grind
  exact eq14444

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation3868 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3868 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
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
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
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
  have eq453 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq479 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  clear eq18
  have eq488 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq471
    | (have j0 := eq471 X0 X1
       grind)
    | exact resolve eq471 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq744 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq488 x y
       grind)
    | exact superpose eq488 eq16
    | (have j1 := eq488 x y
       grind)
    | exact resolve eq16 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq488 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq3318 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq479 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq479
    | exact resolve eq479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq3367 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3318 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3318
    | (have j0 := eq3318 X0 X1
       grind)
    | exact resolve eq3318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318
  have eq6743 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq744
       have i₂ := eq3367 y x
       grind)
    | exact superpose eq3367 eq744
    | (have j1 := eq3367 y x
       grind)
    | (have r₁ := eq744
       have r₂ := eq3367 y x
       grind)
    | (have r₁ := eq744
       have r₂ := eq3367 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq744
       have r₂ := eq3367 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq744 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq3367
  have eq6744 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6743
  have eq6766 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq753 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq753
    | (have j0 := eq753 (τ X1) (τ X0)
       grind)
    | exact resolve eq753 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq6824 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6766 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq6766
    | (have j0 := eq6766 X0 X1
       grind)
    | exact resolve eq6766 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6766
  have eq6860 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6824 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6824
    | (have j0 := eq6824 X0 X1
       grind)
    | exact resolve eq6824 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6824
  have eq6893 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6860 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6860
    | (have j0 := eq6860 X0 X1
       grind)
    | exact resolve eq6860 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6860
  have eq6919 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6893 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6893
    | (have j0 := eq6893 X0 X1
       grind)
    | exact resolve eq6893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6893
  have eq6939 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6919 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq6919
    | (have j0 := eq6919 X0 X1
       grind)
    | exact resolve eq6919 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6919
  have eq6958 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6939 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6939
    | (have j0 := eq6939 X0 X1
       grind)
    | exact resolve eq6939 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6939
  have eq6971 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6958 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6958
    | (have j0 := eq6958 X0 X1
       grind)
    | exact resolve eq6958 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6958
  have eq15002 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6744
       grind)
    | exact superpose eq6744 eq16
    | exact resolve eq16 eq6744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6744
  have eq15003 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15002
       have r₂ := eq22 x
       grind)
    | exact resolve eq15002 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15002
  have eq15005 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15003
       grind)
    | exact superpose eq15003 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15003
       grind)
    | exact resolve eq13 eq15003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15003
  have eq15008 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15005
  have eq17126 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15008
       grind)
    | exact superpose eq15008 eq16
    | exact resolve eq16 eq15008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15008
  have eq17127 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq17126
       have r₂ := eq22 x
       grind)
    | exact resolve eq17126 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17126
  have eq17130 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq453 x (σ y)
       have i₂ := eq17127
       grind)
    | exact superpose eq17127 eq453
    | (have j0 := eq453 x (σ y)
       grind)
    | (have r₁ := eq453 x (σ y)
       have r₂ := eq17127
       grind)
    | exact resolve eq453 eq17127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17127
  have eq17143 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq17130
  have eq17144 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq17143
  have eq17151 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17144
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17144
    | exact resolve eq17144 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17144
  have eq17162 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq753 x y
       have i₂ := eq17151
       grind)
    | exact superpose eq17151 eq753
    | (have j0 := eq753 x y
       grind)
    | (have r₁ := eq753 x y
       have r₂ := eq17151
       grind)
    | exact resolve eq753 eq17151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17151
  have eq17188 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq17162
  have eq17189 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq17188
  have eq17193 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq753 x y
       grind)
    | (have r₁ := eq17189
       have r₂ := eq753 x y
       grind)
    | exact resolve eq17189 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq17189
  have eq17196 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17193
       grind)
    | exact superpose eq17193 eq16
    | exact resolve eq16 eq17193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17197 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq453 x (σ y)
       have i₂ := eq17193
       grind)
    | exact superpose eq17193 eq453
    | (have j0 := eq453 x (σ y)
       grind)
    | (have r₁ := eq453 x (σ y)
       have r₂ := eq17193
       grind)
    | exact resolve eq453 eq17193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq17193
  have eq17210 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq17197
  have eq17211 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq17210
  have eq17218 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17211
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17211
    | exact resolve eq17211 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17211
  have eq17227 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17218
       grind)
    | exact superpose eq17218 eq10
    | exact resolve eq10 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17218
  have eq17393 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17227
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17227
    | exact resolve eq17227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17227
  have eq17395 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17393
       grind)
    | exact superpose eq17393 eq16
    | exact resolve eq16 eq17393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17393
  have eq17396 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq17395
       have r₂ := eq22 x
       grind)
    | exact resolve eq17395 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17395
  have eq17409 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq17396
       grind)
    | exact superpose eq17396 eq10
    | exact resolve eq10 eq17396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17396
  have eq17576 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq17409
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq17409
    | exact resolve eq17409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17409
  have eq17605 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq6971 y x
       have i₂ := eq17576
       grind)
    | exact superpose eq17576 eq6971
    | (have j0 := eq6971 y x
       grind)
    | (have r₁ := eq6971 y x
       have r₂ := eq17576
       grind)
    | exact resolve eq6971 eq17576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6971 eq17576
  have eq17608 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17605
  have eq17612 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17196
       have i₂ := eq17608
       grind)
    | exact superpose eq17608 eq17196
    | exact resolve eq17196 eq17608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17196 eq17608
  have eq17621 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq17612
  have eq17622 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17621
       grind)
    | exact superpose eq17621 eq16
    | exact resolve eq16 eq17621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17621
  have eq17625 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq17622
       have r₂ := eq22 x
       grind)
    | exact resolve eq17622 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17622
  have eq17626 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17625
       grind)
    | exact superpose eq17625 eq16
    | exact resolve eq16 eq17625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17627 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17625
       grind)
    | exact superpose eq17625 eq10
    | exact resolve eq10 eq17625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17625
  have eq17793 : x = y := by
    first
    | (have i₁ := eq17627
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17627
    | exact resolve eq17627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17627
  have eq17794 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17626
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq17626
    | exact resolve eq17626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17626
  have eq17795 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17794
       have i₂ := eq17793
       grind)
    | exact superpose eq17793 eq17794
    | exact resolve eq17794 eq17793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17793 eq17794
  have eq17796 : False := by grind
  exact eq17796

/-- `Equation3874`: `x ◇ x = (x ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pxy_pyx_pxx_pxy_Equation3874 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3874 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3874.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq58 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq63 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq91 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq130 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq209 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq217 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63 eq217
    | exact resolve eq217 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq222 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq130 X0 X0
       have i₂ := eq209 X0
       grind)
    | exact superpose eq209 eq130
    | exact resolve eq130 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq223 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq209 (σ X0)
       grind)
    | exact superpose eq209 eq15
    | exact resolve eq15 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq223 X0
       have i₂ := eq209 X0
       grind)
    | exact superpose eq209 eq223
    | exact resolve eq223 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq225 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq222 X0
       have i₂ := eq209 (τ X0)
       grind)
    | exact superpose eq209 eq222
    | exact resolve eq222 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq222
  have eq893 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq926 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq63
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq63
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq927 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq926
    | exact resolve eq926 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq929 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq927
    | exact resolve eq927 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq1795 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq893 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq893
    | (have j0 := eq893 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq893 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq113576 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1795 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1795
    | (have j0 := eq1795 x y
       grind)
    | exact resolve eq1795 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq113633 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq20 eq113576
    | exact resolve eq113576 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113576
  have eq113634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq113633
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq113633
    | exact resolve eq113633 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113633
  have eq113635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq113634
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq113634
    | exact resolve eq113634 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113634
  have eq113636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq26 eq113635
    | exact resolve eq113635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113635
  have eq113637 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq113636
       have r₂ := eq27
       grind)
    | exact resolve eq113636 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113636
  have eq113638 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq113637
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq113637
    | exact resolve eq113637 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113637
  have eq113639 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq113638
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq113638
    | exact resolve eq113638 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113638
  have eq113640 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq26 eq113639
    | exact resolve eq113639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113639
  have eq113641 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq113640
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq113640
    | exact resolve eq113640 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113640
  have eq113642 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq113641
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq113641
    | exact resolve eq113641 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113641
  have eq113690 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq113642 eq225
    | exact resolve eq225 eq113642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113642
  have eq113776 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq39 eq113690
    | exact resolve eq113690 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113690
  have eq113792 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq113776
       have i₂ := eq225 sF2
       grind)
    | exact superpose eq225 eq113776
    | exact resolve eq113776 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113776
  have eq113795 : (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq38 eq113792
    | exact resolve eq113792 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113792
  have eq113796 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq113795
  have eq113799 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq113796 eq219
    | (have r₁ := eq219
       have r₂ := eq113796
       grind)
    | exact resolve eq219 eq113796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq113821 : (M.op (τ (σ x)) (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq113796 eq225
    | exact resolve eq225 eq113796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113796
  have eq113892 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq113799
  have eq113902 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq38 eq113821
    | exact resolve eq113821 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq113821
  have eq148227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq113892
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq113892
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq113892 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113892
  have eq148294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq148227
  have eq148307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq148294
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq148294
    | exact resolve eq148294 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148294
  have eq148309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq148307
    | exact resolve eq148307 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148307
  have eq148310 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq148309
       have r₂ := eq27
       grind)
    | exact resolve eq148309 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148309
  have eq148311 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq148310
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq148310
    | exact resolve eq148310 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148310
  have eq148312 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq148311
  have eq148333 : (M.op (τ (σ y)) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq148312 eq225
    | exact resolve eq225 eq148312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148312
  have eq148431 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq39 eq148333
    | exact resolve eq148333 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148333
  have eq148506 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq148431 eq113902
    | exact resolve eq113902 eq148431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113902 eq148431
  have eq148833 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq148506
  have eq148908 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq148833
       grind)
    | exact superpose eq148833 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq148833
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq148833
       grind)
    | exact resolve eq12 eq148833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148914 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq224 y
       have i₂ := eq148833
       grind)
    | exact superpose eq148833 eq224
    | exact resolve eq224 eq148833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148833
  have eq149006 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq148914
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq148914
    | exact resolve eq148914 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148914
  have eq149018 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq149006
       have i₂ := eq224 x
       grind)
    | exact superpose eq224 eq149006
    | exact resolve eq149006 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149006
  have eq149030 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq149018
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq149018
    | exact resolve eq149018 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149018
  have eq149151 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq149030 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq149030
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq149030
       grind)
    | exact resolve eq12 eq149030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149030
  have eq168481 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq148908 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148908
  have eq168493 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq168481
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq168481
    | exact resolve eq168481 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168481
  have eq193305 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq149151 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149151
  have eq193311 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq58 eq193305
    | exact resolve eq193305 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193305
  have eq193315 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq193311
    | exact resolve eq193311 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193311
  have eq193316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq193315
       have i₂ := eq168493
       grind)
    | exact superpose eq168493 eq193315
    | exact resolve eq193315 eq168493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168493 eq193315
  have eq193456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq193316
  have eq193467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq193456
    | exact resolve eq193456 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193456
  have eq193471 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq193467
       have r₂ := eq27
       grind)
    | exact resolve eq193467 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193467
  have eq193474 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq216
       have i₂ := eq193471
       grind)
    | exact superpose eq193471 eq216
    | (have r₁ := eq216
       have r₂ := eq193471
       grind)
    | exact resolve eq216 eq193471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq200942 : (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by grind
  clear eq193474
  have eq201005 : (M.op x y) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq200942
       have i₂ := eq193471
       grind)
    | exact superpose eq193471 eq200942
    | exact resolve eq200942 eq193471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200942
  have eq201023 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq201005
       have i₂ := eq193471
       grind)
    | exact superpose eq193471 eq201005
    | exact resolve eq201005 eq193471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201005
  have eq201043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq929
       have i₂ := eq201023
       grind)
    | exact superpose eq201023 eq929
    | exact resolve eq929 eq201023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq201023
  have eq201070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq201043
    | exact resolve eq201043 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201043
  have eq201082 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq201070
       have r₂ := eq27
       grind)
    | exact resolve eq201070 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201070
  have eq201524 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq224 x
       have i₂ := eq193471
       grind)
    | exact superpose eq193471 eq224
    | exact resolve eq224 eq193471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208641 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq201524
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq201524
    | exact resolve eq201524 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq201524
  have eq210094 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq208641
    | exact resolve eq208641 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208641
  have eq211047 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq210094 eq201082
    | exact resolve eq201082 eq210094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201082
  have eq211188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq210094 eq211047
    | exact resolve eq211047 eq210094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211047
  have eq211378 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq211188
       have r₂ := eq27
       grind)
    | exact resolve eq211188 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211188
  have eq217977 : (τ (σ (M.op x y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq211378 eq225
    | exact resolve eq225 eq211378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq211378
  have eq218068 : (τ (σ (M.op x y))) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq39 eq217977
    | exact resolve eq217977 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq217977
  have eq218077 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq37 eq218068
    | exact resolve eq218068 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq218068
  have eq218078 : (M.op x y) = (M.op y y) := by grind
  clear eq218077
  have eq218431 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x y) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq218078
       grind)
    | exact superpose eq218078 eq12
    | (have j0 := eq12 y X0
       grind)
    | exact resolve eq12 eq218078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218437 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq224 y
       have i₂ := eq218078
       grind)
    | exact superpose eq218078 eq224
    | exact resolve eq224 eq218078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq218078
  have eq218554 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq218437
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq218437
    | exact resolve eq218437 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq218437
  have eq218658 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq218554
    | exact resolve eq218554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218554
  have eq219315 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x y)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq218658 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | exact resolve eq12 eq218658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218658
  have eq234969 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq218431 x
       have i₂ := eq193471
       grind)
    | exact superpose eq193471 eq218431
    | (have j0 := eq218431 x
       grind)
    | (have r₁ := eq218431 x
       have r₂ := eq193471
       grind)
    | exact resolve eq218431 eq193471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193471 eq218431
  have eq234977 : (M.op x y) = (k y x) := by grind
  clear eq234969
  have eq234981 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq234977
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq234977
    | exact resolve eq234977 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq234977
  have eq234995 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq58
       have i₂ := eq234981
       grind)
    | exact superpose eq234981 eq58
    | exact resolve eq58 eq234981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq234981
  have eq235003 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq234995
    | exact resolve eq234995 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq234995
  have eq236566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq210094 eq219315
    | (have j0 := eq219315 (σ x)
       grind)
    | (have r₁ := eq219315 (σ x)
       have r₂ := eq210094
       grind)
    | exact resolve eq219315 eq210094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210094 eq219315
  have eq236569 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq236566
  have eq236572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq235003 eq236569
    | exact resolve eq236569 eq235003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235003 eq236569
  have eq236593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq236572
    | exact resolve eq236572 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq236572
  have eq236603 : False := by grind
  exact eq236603

/-- `Equation3874`: `x ◇ x = (x ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_pxx_pyx_Equation3874 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3874 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3874.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X2 X3)) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X0 (M.op (M.op X1 X2) X3))) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X1 X2) X3)) X1 X2
       have i₂ := eq9 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq63 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq77 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq130 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1124 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq58
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq58
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1136 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1124
    | exact resolve eq1124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1138 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X0)) X1 X2 X3
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2638 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X1 x) x)) X0 (M.op (M.op X1 x) x)
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2648 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) (M.op X0 (M.op (M.op X1 X3) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X3) X4)) (M.op X0 (M.op (M.op X1 X3) X4))
       have i₂ := eq54 X0 X1 X3 X4
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2890 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq52 eq2638
    | exact resolve eq2638 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2899 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq2638 X0 (M.op X0 X1)
       grind)
    | exact superpose eq2638 eq9
    | exact resolve eq9 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2925 : (M.op (M.op (M.op x y) (M.op x y)) x) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2890 eq52
    | exact resolve eq52 eq2890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq2929 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq52 eq2925
    | exact resolve eq2925 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2925
  have eq2945 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op X0 (M.op (M.op x y) (M.op x y))) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2929 eq12
    | (have j0 := eq12 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op x y) (M.op x y))
       have r₂ := eq2929
       grind)
    | exact resolve eq12 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2955 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq2945 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945
  have eq3005 : ∀ X0 : G, (k (τ X0) (τ (M.op (M.op x y) (M.op x y)))) = (τ (M.op X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq2955 eq130
    | exact resolve eq130 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq4557 : ∀ X0 : G, (k (τ (M.op X0 (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq77 eq3005
    | exact resolve eq3005 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4561 : (τ (M.op (M.op x y) (M.op x y))) = (k (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq2929 eq3005
    | exact resolve eq3005 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq4595 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (k (τ X0) (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3005 eq4557
    | exact resolve eq4557 eq3005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005 eq4557
  have eq4717 : (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) ∨ (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) ∨ (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq4561 eq14
    | (have j0 := eq14 (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq14 eq4561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4561
  have eq4719 : (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) := by grind
  clear eq4717
  have eq4738 : ∀ X0 : G, (τ (M.op (M.op x y) (M.op x y))) ≠ (τ (M.op (M.op x y) (M.op x y))) ∨ (k X0 (τ (M.op (M.op x y) (M.op x y)))) = (M.op X0 (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4719 eq12
    | (have j0 := eq12 X0 (τ (M.op (M.op x y) (M.op x y)))
       grind)
    | (have r₁ := eq12 X0 (τ (M.op (M.op x y) (M.op x y)))
       have r₂ := eq4719
       grind)
    | exact resolve eq12 eq4719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4747 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4719 eq9
    | exact resolve eq9 eq4719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4749 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) (M.op x y)))) = (M.op X0 (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq4738 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4738
  have eq4782 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (M.op (τ X0) (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4749 eq4595
    | exact resolve eq4595 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4595
  have eq4827 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ X0) (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4749 eq4782
    | exact resolve eq4782 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4749 eq4782
  have eq4847 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq4747 eq4827
    | exact resolve eq4827 eq4747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4747 eq4827
  have eq4924 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq4847 X0
       grind)
    | exact superpose eq4847 eq11
    | exact resolve eq11 eq4847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4965 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4924 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4924
    | exact resolve eq4924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4924
  have eq6110 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1138 X0 X1 (M.op X0 (M.op X0 X0)) (M.op x x)
       have i₂ := eq1138 X0 X0 x x
       grind)
    | exact superpose eq1138 eq1138
    | exact resolve eq1138 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6125 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) ≠ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))
       have i₂ := eq1138 X0 (M.op X0 (M.op X0 X0)) X0 X0
       grind)
    | exact superpose eq1138 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6128 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) X1) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) X1 X2 X3
       have i₂ := eq1138 X0 (M.op X0 (M.op X0 X0)) X0 X0
       grind)
    | exact superpose eq1138 eq54
    | exact resolve eq54 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq6147 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6128 X0 X1 X2 X3
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq6128
    | exact resolve eq6128 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6128
  have eq6150 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6125 X0 X1
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq6125
    | (have j0 := eq6125 X0 X1
       grind)
    | exact resolve eq6125 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq6125
  have eq6176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6147 X0 X1 X2 X3
       have i₂ := eq6110 X0 X0
       grind)
    | exact superpose eq6110 eq6147
    | exact resolve eq6147 eq6110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6147
  have eq6179 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq6150 X0 X1
       grind)
    | (have r₁ := eq6150 X0 X1
       have r₂ := eq6110 X0 X0
       grind)
    | exact resolve eq6150 eq6110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6150
  have eq6187 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6179 X0 X1
       have i₂ := eq6110 X0 X0
       grind)
    | exact superpose eq6110 eq6179
    | exact resolve eq6179 eq6110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6110 eq6179
  have eq6528 : ∀ X0 X1 : G, (k (τ X0) (τ (M.op X1 X1))) = (τ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X0 (M.op X1 X1)
       have i₂ := eq6187 X1 X0
       grind)
    | exact superpose eq6187 eq130
    | exact resolve eq130 eq6187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq6539 : ∀ X0 X1 : G, (k (τ X0) (M.op (τ X1) (τ X1))) = (τ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6528 X0 X1
       have i₂ := eq4847 X1
       grind)
    | exact superpose eq4847 eq6528
    | exact resolve eq6528 eq4847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6528
  have eq6577 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ X1) (τ X1))) = (τ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6539 X0 X1
       have i₂ := eq6187 (τ X1) (τ X0)
       grind)
    | exact superpose eq6187 eq6539
    | exact resolve eq6539 eq6187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6539
  have eq7122 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 X0 X0 X0 X0
       have i₂ := eq2648 X0 X0 X0 X0 X0
       grind)
    | exact superpose eq2648 eq54
    | exact resolve eq54 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7313 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq7122 (M.op x (M.op (M.op x x) x))
       have i₂ := eq2648 x x x x x
       grind)
    | exact superpose eq2648 eq7122
    | exact resolve eq7122 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648 eq7122
  have eq7353 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7313 X0
       have i₂ := eq2899 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq2899 eq7313
    | exact resolve eq7313 eq2899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7313
  have eq7371 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2899 X0 X1
       have i₂ := eq7353 X0
       grind)
    | exact superpose eq7353 eq2899
    | exact resolve eq2899 eq7353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899 eq7353
  have eq7419 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7371 (M.op X0 (M.op (M.op X1 x) x)) (M.op X0 (M.op (M.op X1 x) x))
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq7371
    | exact resolve eq7371 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7515 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6176 X0 X1 X2 X3
       have i₂ := eq7419 X0 (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq7419 eq6176
    | exact resolve eq6176 eq7419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6176 eq7419
  have eq10019 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op (M.op X0 X0) X1) X4) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X4 X5) X6)) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq7515 (M.op X0 (M.op (M.op X1 x) x)) X1 x x
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq7515
    | exact resolve eq7515 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq10165 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 X2) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 (M.op X1 X2) (M.op X0 X0)
       have i₂ := eq7515 X0 X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq7515 eq77
    | exact resolve eq77 eq7515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7515
  have eq10218 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 X2) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10165 X0 X1 X2
       have i₂ := eq7371 X0 X0
       grind)
    | exact superpose eq7371 eq10165
    | exact resolve eq10165 eq7371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7371 eq10165
  have eq10329 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10218 X0 x x
       have i₂ := eq10019 X0 x x x sF0
       grind)
    | exact superpose eq10019 eq10218
    | exact resolve eq10218 eq10019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10218
  have eq10479 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op (M.op X0 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X1 X2)) X1 X2
       have i₂ := eq10329 X0 (M.op X1 X2)
       grind)
    | exact superpose eq10329 eq9
    | exact resolve eq9 eq10329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10329
  have eq10509 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10479 X0 X1 X2
       have i₂ := eq10019 X0 (M.op X1 X2) X0 X0 (M.op X1 X2)
       grind)
    | exact superpose eq10019 eq10479
    | exact resolve eq10479 eq10019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10019 eq10479
  have eq10551 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10509 X0 X1 X2
       have i₂ := eq2638 X0 (M.op X1 X2)
       grind)
    | exact superpose eq2638 eq10509
    | exact resolve eq10509 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638 eq10509
  have eq14367 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op (τ (M.op X0 X0)) (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6577 (M.op X0 X0) X1
       have i₂ := eq10551 X0 X1 X1
       grind)
    | exact superpose eq10551 eq6577
    | exact resolve eq6577 eq10551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6577
  have eq14415 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14367 X0 X1
       have i₂ := eq4847 X0
       grind)
    | exact superpose eq4847 eq14367
    | exact resolve eq14367 eq4847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14367
  have eq14441 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op (M.op (τ X0) (τ X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14415 X0 X1
       have i₂ := eq10551 (τ X0) (τ X1) (τ X1)
       grind)
    | exact superpose eq10551 eq14415
    | exact resolve eq14415 eq10551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10551 eq14415
  have eq15428 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (M.op X0 X0) X1)
       have i₂ := eq14441 X0 X1
       grind)
    | exact superpose eq14441 eq11
    | exact resolve eq11 eq14441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14441
  have eq15662 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) X1) = (σ (M.op (M.op X0 X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15428 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15428
    | exact resolve eq15428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15428
  have eq16784 : ∀ X0 X1 : G, (M.op (M.op (σ X1) (σ X1)) (σ X0)) = (σ (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15662 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15662
    | exact resolve eq15662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15662
  have eq24067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1136
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1136
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq1136 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq24106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24067
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24067
    | exact resolve eq24067 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24067
  have eq24109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq24106
    | exact resolve eq24106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24106
  have eq24110 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24109
       have r₂ := eq27
       grind)
    | exact resolve eq24109 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24109
  have eq24130 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24110 eq4847
    | exact resolve eq4847 eq24110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24110
  have eq24182 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39 eq24130
    | exact resolve eq24130 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq24130
  have eq24183 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq24182
  have eq24211 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24183 eq4847
    | exact resolve eq4847 eq24183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4847 eq24183
  have eq24263 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq24211
    | exact resolve eq24211 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq24211
  have eq24264 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq24263
  have eq24298 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4965 y
       have i₂ := eq24264
       grind)
    | exact superpose eq24264 eq4965
    | exact resolve eq4965 eq24264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24301 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6187 y x
       have i₂ := eq24264
       grind)
    | exact superpose eq24264 eq6187
    | exact resolve eq6187 eq24264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24264
  have eq24339 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24298
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24298
    | exact resolve eq24298 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24298
  have eq24369 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq24339 eq6187
    | exact resolve eq6187 eq24339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6187 eq24339
  have eq25637 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24369 eq63
    | exact resolve eq63 eq24369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq24369
  have eq25711 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq25637
    | exact resolve eq25637 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25637
  have eq25732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25711
       have i₂ := eq24301 x
       grind)
    | exact superpose eq24301 eq25711
    | exact resolve eq25711 eq24301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24301 eq25711
  have eq25765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq25732
  have eq25770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25765
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25765
    | exact resolve eq25765 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25765
  have eq25775 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq25770
    | exact resolve eq25770 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25770
  have eq25778 : x = (M.op x x) := by
    first
    | (have r₁ := eq25775
       have r₂ := eq27
       grind)
    | exact resolve eq25775 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25775
  have eq26053 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4965 x
       have i₂ := eq25778
       grind)
    | exact superpose eq25778 eq4965
    | exact resolve eq4965 eq25778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4965
  have eq26072 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16784 X0 x
       have i₂ := eq25778
       grind)
    | exact superpose eq25778 eq16784
    | exact resolve eq16784 eq25778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16784 eq25778
  have eq26091 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26072 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26072
    | (have j0 := eq26072 X0
       grind)
    | exact resolve eq26072 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26072
  have eq26992 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26053
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26053
    | exact resolve eq26053 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26053
  have eq27697 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq26992 eq26091
    | exact resolve eq26091 eq26992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26091 eq26992
  have eq37776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27697 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27697
    | (have j0 := eq27697 y
       grind)
    | exact resolve eq27697 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq27697
  have eq37851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37776
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37776
    | exact resolve eq37776 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37776
  have eq37867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq37851
    | exact resolve eq37851 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37851
  have eq37875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq37867
    | exact resolve eq37867 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37867
  have eq37879 : False := by grind
  exact eq37879
