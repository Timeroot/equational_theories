import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxy_pyx_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq110
    | (have j0 := eq110 (σ X0)
       grind)
    | exact resolve eq110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq44
    | (have j1 := eq110 x
       grind)
    | exact resolve eq44 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq3505 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq402 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq18688 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 X0)) (M.op y x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq14
    | exact resolve eq14 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq18691 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18688 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq18688
    | exact resolve eq18688 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18688
  have eq18822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq18691 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq18691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18822
    | exact resolve eq18822 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18822
  have eq18834 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18823
       have r₂ := eq28
       grind)
    | exact resolve eq18823 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18823
  have eq18860 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq18834 eq14
    | exact resolve eq14 eq18834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18834
  have eq18863 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18860 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq18860
    | exact resolve eq18860 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18860
  have eq18868 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq18863
  have eq18894 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18868
    | exact resolve eq18868 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18868
  have eq19119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq18894 eq18691
    | exact resolve eq18691 eq18894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18691 eq18894
  have eq19121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq19119
  have eq19123 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19121
       have r₂ := eq28
       grind)
    | exact resolve eq19121 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19121
  have eq19129 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19123
  have eq19154 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19129
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19129
    | exact resolve eq19129 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19129
  have eq19350 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19154
       grind)
    | exact superpose eq19154 eq45
    | exact resolve eq45 eq19154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19154
  have eq19368 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq19350
    | exact resolve eq19350 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19350
  have eq19405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19368 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq19368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq19405
    | exact resolve eq19405 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19405
  have eq19419 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19408
       have r₂ := eq28
       grind)
    | exact resolve eq19408 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19408
  have eq55959 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq19419 eq14
    | exact resolve eq14 eq19419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19419
  have eq55973 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55959 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq55959
    | exact resolve eq55959 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55959
  have eq55974 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq55973
  have eq56304 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq55974
  have eq56346 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq56304
    | exact resolve eq56304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56304
  have eq56369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq56346 eq19368
    | exact resolve eq19368 eq56346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19368 eq56346
  have eq56403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq56369
  have eq56415 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq56403
       have r₂ := eq28
       grind)
    | exact resolve eq56403 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56403
  have eq56418 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq56415 eq30
    | exact resolve eq30 eq56415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq56415
  have eq56545 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq56418
    | exact resolve eq56418 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq56418
  have eq56546 : x = y := by grind
  clear eq56545
  have eq56825 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq56546
       grind)
    | exact superpose eq56546 eq19
    | exact resolve eq19 eq56546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq56826 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq56546
       grind)
    | exact superpose eq56546 eq25
    | exact resolve eq25 eq56546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq56546
  have eq57041 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq56826
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq56826
    | exact resolve eq56826 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56826
  have eq57042 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq57041 eq27
    | exact resolve eq27 eq57041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq57041
  have eq57172 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq406
       have i₂ := eq56825
       grind)
    | exact superpose eq56825 eq406
    | exact resolve eq406 eq56825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq57183 : (M.op (M.op x y) x) = (k (M.op x y) x) := by grind
  have eq57217 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq57172
    | exact resolve eq57172 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57172
  have eq57227 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq57822 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57217 eq110
    | (have j0 := eq110 (σ x)
       grind)
    | exact resolve eq110 eq57217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq57823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57042 eq57822
    | exact resolve eq57822 eq57042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57822
  have eq57837 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq57823
       have r₂ := eq28
       grind)
    | exact resolve eq57823 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57823
  have eq57843 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57042 eq57837
    | exact resolve eq57837 eq57042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57837
  have eq57854 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57843 eq57227
    | exact resolve eq57227 eq57843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57227 eq57843
  have eq57858 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57042 eq57854
    | exact resolve eq57854 eq57042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57854
  have eq58516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57858 eq57217
    | exact resolve eq57217 eq57858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57217 eq57858
  have eq58521 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq58516
  have eq58524 : x = (M.op x y) := by
    first
    | (have r₁ := eq58521
       have r₂ := eq28
       grind)
    | exact resolve eq58521 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58521
  have eq58536 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq58524 eq21
    | exact resolve eq21 eq58524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq58661 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq58524 eq57183
    | exact resolve eq57183 eq58524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57183
  have eq58670 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq58661
       have i₂ := eq56825
       grind)
    | exact superpose eq56825 eq58661
    | exact resolve eq58661 eq56825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56825 eq58661
  have eq58781 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq58536
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq58536
    | exact resolve eq58536 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58536
  have eq58785 : x = (k x x) := by
    first
    | exact superpose eq58524 eq58670
    | exact resolve eq58670 eq58524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58524 eq58670
  have eq59149 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3505 x
       have i₂ := eq58785
       grind)
    | exact superpose eq58785 eq3505
    | (have j0 := eq3505 x
       grind)
    | exact resolve eq3505 eq58785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505 eq58785
  have eq59153 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq59149
  have eq59160 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq59153
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq59153
    | exact resolve eq59153 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq59153
  have eq59175 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57042 eq59160
    | exact resolve eq59160 eq57042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57042 eq59160
  have eq59188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58781 eq59175
    | exact resolve eq59175 eq58781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58781 eq59175
  have eq59199 : False := by grind
  exact eq59199

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pxy_Equation1996 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  clear eq18
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
  have eq49 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (M.op X1 X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq100
    | (have j0 := eq100 X0 X1
       grind)
    | exact resolve eq100 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq130 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (τ (M.op X0 X0))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (τ (τ (M.op X0 X0)))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130 (τ X0) X1 X2
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq130
    | exact resolve eq130 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq307 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105 x y
       grind)
    | exact superpose eq105 eq16
    | (have j1 := eq105 x y
       grind)
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq450 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (M.op X0 X0)))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq238 (M.op x (τ (τ (M.op X0 X0)))) X1 X3
       have i₂ := eq238 X0 x (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq238 eq238
    | exact resolve eq238 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (M.op X0 X0))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq130 (M.op x (τ (τ (M.op X0 X0)))) X1 X3
       have i₂ := eq238 X0 x (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq238 eq130
    | exact resolve eq130 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq858 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq480 (M.op x (τ (τ (τ (M.op X0 X0))))) X1 X3
       have i₂ := eq480 X0 x (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact superpose eq480 eq480
    | exact resolve eq480 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ X1) (τ (τ (τ (M.op X0 X0))))) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 (M.op x (τ (τ (τ (M.op X0 X0)))))
       have i₂ := eq480 X0 x (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact superpose eq480 eq49
    | exact resolve eq49 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq904 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (M.op X0 X0))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq238 (M.op x (τ (τ (τ (M.op X0 X0))))) X1 X3
       have i₂ := eq480 X0 x (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact superpose eq480 eq238
    | exact resolve eq238 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq480
  have eq3275 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq307
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq307
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq307
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq307
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq307 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq3276 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3275
  have eq6791 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq450 (M.op x (τ (τ (τ (τ (τ (M.op X0 X0))))))) X1 X3
       have i₂ := eq904 X0 x (τ (τ (τ (τ (τ (M.op X0 X0))))))
       grind)
    | exact superpose eq904 eq450
    | exact resolve eq450 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq904
  have eq22307 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ X1) (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq894 (M.op x (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))) X1
       have i₂ := eq858 X0 x (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))
       grind)
    | exact superpose eq858 eq894
    | exact resolve eq894 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq894
  have eq67195 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3276
       grind)
    | exact superpose eq3276 eq16
    | exact resolve eq16 eq3276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3276
  have eq67196 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq67195
       have r₂ := eq22 x
       grind)
    | exact resolve eq67195 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67195
  have eq500502 : ∀ X0 : G, y = (M.op (M.op x (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))) (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq6791 X0 x y
       have i₂ := eq67196
       grind)
    | exact superpose eq67196 eq6791
    | exact resolve eq6791 eq67196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67196
  have eq500506 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq500502 x
       have i₂ := eq6791 x x x
       grind)
    | (have i₁ := eq500502 x
       have i₂ := eq6791 x x (M.op (M.op x (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op x x))))))))))) (M.op x x))
       grind)
    | exact superpose eq6791 eq500502
    | exact resolve eq500502 eq6791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500502
  have eq501112 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq500506
       grind)
    | exact superpose eq500506 eq16
    | exact resolve eq16 eq500506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500506
  have eq501113 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq501112
       have r₂ := eq22 x
       grind)
    | exact resolve eq501112 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501112
  have eq501146 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))) (σ (M.op x x))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6791 X0 (σ x) (σ y)
       have i₂ := eq501113
       grind)
    | exact superpose eq501113 eq6791
    | exact resolve eq6791 eq501113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6791 eq501113
  have eq501160 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq501146 x
       have i₂ := eq22307 x x
       grind)
    | exact superpose eq22307 eq501146
    | exact resolve eq501146 eq22307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22307 eq501146
  have eq501161 : (σ x) = (σ y) := by grind
  clear eq501160
  have eq501772 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq501161
       grind)
    | exact superpose eq501161 eq16
    | exact resolve eq16 eq501161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501773 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq501161
       grind)
    | exact superpose eq501161 eq10
    | exact resolve eq10 eq501161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501161
  have eq501927 : x = y := by
    first
    | (have i₁ := eq501773
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq501773
    | exact resolve eq501773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501773
  have eq501928 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq501772
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq501772
    | exact resolve eq501772 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq501772
  have eq501929 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq501928
       have i₂ := eq501927
       grind)
    | exact superpose eq501927 eq501928
    | exact resolve eq501928 eq501927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501927 eq501928
  have eq501930 : False := by grind
  exact eq501930

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyy_pxy_Equation1996 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X3 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
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
  have eq77 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq97 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq93
  have eq98 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq97
  have eq130 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 X0
       have i₂ := eq11 X0 (τ X1)
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 X0 (τ X1)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq691 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq70
  have eq807 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq691 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq691
    | (have j0 := eq691 X0 y
       grind)
    | exact resolve eq691 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq5632 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (M.op y X0) ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq30 eq336
    | exact resolve eq336 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq5673 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (M.op y X0) ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq41 eq5632
    | (have j0 := eq5632 X0
       grind)
    | exact resolve eq5632 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq5632
  have eq6095 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq807 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq807
    | (have j0 := eq807 x
       grind)
    | exact resolve eq807 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq6105 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6095
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq6095
    | exact resolve eq6095 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6095
  have eq6124 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq6105
    | exact resolve eq6105 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6105
  have eq6132 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6124
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq6124
    | exact resolve eq6124 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq6124
  have eq18373 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq77
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq18382 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq18373
  have eq18383 : (k x y) = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq18382
  have eq21222 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6132 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6132
       grind)
    | exact resolve eq12 eq6132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6132
  have eq21233 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq21222
  have eq21234 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq21233
  have eq23088 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq18383
       grind)
    | exact superpose eq18383 eq49
    | exact resolve eq49 eq18383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq18383
  have eq23117 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq23088
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq23088
    | exact resolve eq23088 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq23088
  have eq23155 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq21234
  have eq25568 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23117
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq23117
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq23117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23117
  have eq25594 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq25568
    | exact resolve eq25568 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25568
  have eq25595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq25594
    | exact resolve eq25594 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25594
  have eq25596 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq25595
       have r₂ := eq28
       grind)
    | exact resolve eq25595 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25595
  have eq25598 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ x) (σ x))) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq25596 eq14
    | exact resolve eq14 eq25596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25596
  have eq25721 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq25598 eq57
    | exact resolve eq57 eq25598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq25598
  have eq25788 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25721 eq23155
    | (have j1 := eq25721 (σ y)
       grind)
    | (have r₁ := eq23155
       have r₂ := eq25721 (σ y)
       grind)
    | (have r₁ := eq23155
       have r₂ := eq25721 x
       grind)
    | exact resolve eq23155 eq25721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25949 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq25721 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25721
  have eq25951 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq25788
  have eq25953 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq25949
       have r₂ := eq27
       grind)
    | exact resolve eq25949 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25949
  have eq26065 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq25951
       have r₂ := eq23155
       grind)
    | exact resolve eq25951 eq23155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23155 eq25951
  have eq26087 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq26065
       have r₂ := eq27
       grind)
    | exact resolve eq26065 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26065
  have eq26096 : (τ (M.op (σ x) (σ y))) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25953 eq130
    | exact resolve eq130 eq25953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq26106 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 X1)) = X1 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq25953 eq14
    | exact resolve eq14 eq25953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25953
  have eq26236 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26087 eq61
    | exact resolve eq61 eq26087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq26087
  have eq26698 : y = (M.op (M.op y (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26106 y y
       have i₂ := eq26096
       grind)
    | exact superpose eq26096 eq26106
    | exact resolve eq26106 eq26096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26096
  have eq26856 : y = (M.op (M.op y (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq26698
  have eq120796 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5673 x
       have i₂ := eq26236
       grind)
    | exact superpose eq26236 eq5673
    | (have j0 := eq5673 x
       grind)
    | exact resolve eq5673 eq26236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5673 eq26236
  have eq120989 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq120796
  have eq121101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120989
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq120989
    | exact resolve eq120989 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120989
  have eq121118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq121101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq121101
    | exact resolve eq121101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121101
  have eq121125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq121118
    | exact resolve eq121118 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121118
  have eq121127 : (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq121125
       have r₂ := eq28
       grind)
    | exact resolve eq121125 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121125
  have eq121140 : x = (M.op (M.op y (M.op (σ x) (σ y))) (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26106 y x
       have i₂ := eq121127
       grind)
    | exact superpose eq121127 eq26106
    | exact resolve eq26106 eq121127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26106 eq121127
  have eq121153 : x = (M.op (M.op y (M.op (σ x) (σ y))) (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq121140
  have eq121160 : ∀ X0 : G, (M.op x (M.op (M.op y (M.op (σ x) (σ y))) X0)) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq121153 eq14
    | exact resolve eq14 eq121153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121153
  have eq121201 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26856 eq121160
    | exact resolve eq121160 eq26856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26856 eq121160
  have eq121276 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq121201
  have eq121278 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq121276
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq121276
    | exact resolve eq121276 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121276
  have eq121690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq121278 eq15
    | exact resolve eq15 eq121278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121278
  have eq121997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq121690
    | exact resolve eq121690 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121690
  have eq122000 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq121997
       have r₂ := eq28
       grind)
    | exact resolve eq121997 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121997
  have eq122002 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq122000 eq30
    | exact resolve eq30 eq122000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq122000
  have eq122153 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq122002
    | exact resolve eq122002 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq122002
  have eq122154 : x = y := by grind
  clear eq122153
  have eq122173 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq122154
       grind)
    | exact superpose eq122154 eq19
    | exact resolve eq19 eq122154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq122174 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq122154
       grind)
    | exact superpose eq122154 eq25
    | exact resolve eq25 eq122154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq122154
  have eq122456 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq122174
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq122174
    | exact resolve eq122174 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq122174
  have eq122900 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq122456 eq27
    | exact resolve eq27 eq122456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq122456
  have eq125925 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq122900 eq69
    | exact resolve eq69 eq122900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq122900
  have eq126192 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq125925
       have i₂ := eq122173
       grind)
    | exact superpose eq122173 eq125925
    | exact resolve eq125925 eq122173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122173 eq125925
  have eq126285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq126192 eq15
    | exact resolve eq15 eq126192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126192
  have eq126609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq126285
    | exact resolve eq126285 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq126285
  have eq126710 : False := by grind
  exact eq126710

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq54
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq61
  have eq151 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq155 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq151 X1 X1
       have r₂ := eq63 X1 X1
       grind)
    | exact resolve eq151 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq151
  have eq374 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq155 (σ X0) (σ X1)
       grind)
    | exact superpose eq155 eq15
    | exact resolve eq15 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq374
    | exact resolve eq374 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq374
  have eq381 : False := by grind
  exact eq381

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq44 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq51
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq62 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq62
  have eq158 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq253 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X0) X3 X4
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq9 (M.op X2 X2) X1 X2
       have i₂ := eq19 X2 X2 X2
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2917 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq253 X0 X1 X2 X3 X4
       have i₂ := eq65 X0 X1
       grind)
    | (have i₁ := eq253 X1 X1 X2 X3 X4
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq253
    | (have j1 := eq65 X0 X1
       grind)
    | exact resolve eq253 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq3043 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) ≠ (M.op X0 X5) ∨ (M.op X0 X5) = (k X0 X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq158 X0 X5
       have i₂ := eq253 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq253 eq158
    | (have j0 := eq158 X0 X5
       grind)
    | exact resolve eq158 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq253
  have eq3243 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2917 X0 X1 x x x
       have j1 := eq3043 X0 X1 x x x X1
       grind)
    | (have r₁ := eq2917 X0 X1 x x x
       have r₂ := eq3043 X0 X1 x x x X1
       grind)
    | exact resolve eq2917 eq3043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917 eq3043
  have eq90120 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3243 (σ X0) (σ X1)
       grind)
    | exact superpose eq3243 eq15
    | exact resolve eq15 eq3243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90139 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90120 X0 X1
       have i₂ := eq3243 X0 X1
       grind)
    | exact superpose eq3243 eq90120
    | exact resolve eq90120 eq3243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243 eq90120
  have eq90167 : False := by grind
  exact eq90167

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq39 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq53 (M.op x x)
       have r₂ := eq12 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 (k x x) x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq57
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq115 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq39 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq39
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq39 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq118 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq131 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq12 (σ (M.op X0 X0)) (σ X0)
       have r₂ := eq64 X0
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq879 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq887 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq879 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq892 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq887 X0 X1
       have j1 := eq131 X1 (σ X0)
       grind)
    | (have r₁ := eq887 (M.op X0 X0) X1
       have r₂ := eq131 X0 (M.op (σ X1) (σ X1))
       grind)
    | (have r₁ := eq887 (M.op X0 X0) X1
       have r₂ := eq131 X0 (σ (M.op X1 X1))
       grind)
    | (have r₁ := eq887 X0 X0
       have r₂ := eq131 X0 (σ X0)
       grind)
    | exact resolve eq887 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq887
  have eq906 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq892 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq892 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq892 X0 X0
       have r₂ := eq12 (k (σ X0) (σ X0)) (σ X0)
       grind)
    | (have r₁ := eq892 X0 X0
       have r₂ := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | exact resolve eq892 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq916 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq906 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq906
    | (have j0 := eq906 X0 X1
       grind)
    | exact resolve eq906 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq917 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq916 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq944 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq917 x y
       grind)
    | exact superpose eq917 eq16
    | exact resolve eq16 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq1038 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq944
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq944
    | (have j1 := eq118 x y
       grind)
    | exact resolve eq944 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1042 : (M.op x y) = (M.op y x) := by grind
  clear eq1038
  have eq1125 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1042
       grind)
    | exact superpose eq1042 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1042
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1042
       grind)
    | exact resolve eq13 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1132 : x = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq1125
  have eq1134 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1132
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1132 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1212 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq944
       have i₂ := eq1134
       grind)
    | exact superpose eq1134 eq944
    | exact resolve eq944 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq1134
  have eq1213 : False := by grind
  exact eq1213

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq192 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq195 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq192 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq192 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq1649 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq195
  have eq1710 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq1812 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1710 (σ X0) (σ X1)
       grind)
    | exact superpose eq1710 eq15
    | exact resolve eq15 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1819 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1812 X0 X1
       have i₂ := eq1710 X0 X1
       grind)
    | exact superpose eq1710 eq1812
    | exact resolve eq1812 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710 eq1812
  have eq1825 : False := by grind
  exact eq1825

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pyx_pxy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X1 X1) X2)) X1) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X1) X2) (M.op X2 x)
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X1 X2 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = (M.op (M.op X1 X4) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30 X1 X4 X3
       have i₂ := eq30 X1 X2 X0
       grind)
    | (have i₁ := eq30 X2 X1 X2
       have i₂ := eq30 X2 X2 X2
       grind)
    | exact superpose eq30 eq30
    | exact resolve eq30 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X1 X2) (M.op X2 X0))) X1) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32 X1 (M.op X1 X1) X3
       have i₂ := eq30 X1 X2 X0
       grind)
    | (have i₁ := eq32 X1 (M.op X1 X2) X3
       have i₂ := eq30 X1 X1 X2
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq189 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X3) (M.op X3 X2)) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq225 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq445 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 x X1 X2 (M.op X1 X2)
       have i₂ := eq74 (M.op X2 x) (M.op X1 X2) (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq87 x X1 X2 (M.op X1 X2)
       have i₂ := eq74 X3 (M.op X1 X2) X0 (M.op X2 x) (M.op X1 X2)
       grind)
    | exact superpose eq74 eq87
    | exact resolve eq87 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq87
  have eq689 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq225 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (k X0 X3) ∨ (M.op (M.op (M.op X0 X3) X1) (M.op X1 X2)) = X3 ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X1 X2 X3
    grind
  clear eq189
  have eq908 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) X1) (M.op X1 X2)) = X3 ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq870 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq5955 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X3 X3) X2)) X3) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66 (M.op (M.op X0 X3) (M.op X0 X3)) X1 X2
       have i₂ := eq908 X0 (M.op X0 X3) (M.op X0 X3) X3
       grind)
    | exact superpose eq908 eq66
    | (have j1 := eq908 X0 X1 X2 X1
       grind)
    | exact resolve eq66 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq908
  have eq6020 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5955 X0 X1 x x
       have i₂ := eq32 x x (M.op X0 X1)
       grind)
    | (have i₁ := eq5955 X0 X1 x x
       have i₂ := eq32 X1 x (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op x x) x)) x)
       grind)
    | exact superpose eq32 eq5955
    | (have j0 := eq5955 X0 X1 x x
       grind)
    | exact resolve eq5955 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq5955
  have eq6276 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 X1) X2) (M.op X2 X3)) X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq445 X0 X1 X1 X3
       have i₂ := eq6020 X0 X1
       grind)
    | (have i₁ := eq445 X0 X0 X1 X3
       have i₂ := eq6020 X0 X1
       grind)
    | exact superpose eq6020 eq445
    | (have j1 := eq6020 X0 X1
       grind)
    | exact resolve eq445 eq6020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq6020
  have eq6363 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6276 X0 X1 x x
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq6276
    | (have j0 := eq6276 X0 X1 x x
       grind)
    | exact resolve eq6276 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6276
  have eq8140 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6363 X0 X1
       have i₂ := eq225 X0 X1
       grind)
    | exact superpose eq225 eq6363
    | (have j0 := eq6363 X0 X1
       have j1 := eq225 X0 X1
       grind)
    | exact resolve eq6363 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq6363
  have eq8407 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq8140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8140
  have eq8414 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq8407 X0 X1
       have j1 := eq689 X0 X1
       grind)
    | (have r₁ := eq8407 X0 X1
       have r₂ := eq689 X0 X1
       grind)
    | (have r₁ := eq8407 X0 X0
       have r₂ := eq689 X0 X0
       grind)
    | (have r₁ := eq8407 (M.op X1 X0) X1
       have r₂ := eq689 X0 X1
       grind)
    | exact resolve eq8407 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq8407
  have eq8482 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq8414
  have eq8619 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq8482 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8482
  have eq8761 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq8619 (σ X0) (σ X1)
       grind)
    | exact superpose eq8619 eq15
    | exact resolve eq15 eq8619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8774 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8761 X0 X1
       have i₂ := eq8619 X0 X1
       grind)
    | exact superpose eq8619 eq8761
    | exact resolve eq8761 eq8619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8619 eq8761
  have eq8954 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8774 y x
       grind)
    | exact superpose eq8774 eq16
    | (have r₁ := eq16
       have r₂ := eq8774 y x
       grind)
    | exact resolve eq16 eq8774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8774
  have eq9022 : False := by grind
  exact eq9022
