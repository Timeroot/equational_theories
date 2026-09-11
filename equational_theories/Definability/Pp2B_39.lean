import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_x_pyy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq16 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq16 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq178 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq180 : ∀ X0 : G, (M.op (M.op y (M.op x y)) x) ≠ (M.op (M.op y (M.op x y)) x) ∨ (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | exact superpose eq174 eq13
    | (have j0 := eq13 X0 (M.op (M.op y (M.op x y)) x)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op y (M.op x y)) x)
       have r₂ := eq174 (M.op (M.op y (M.op x y)) x)
       grind)
    | exact resolve eq13 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq183 : ∀ X0 : G, (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ≠ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       have r₂ := eq175 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq187 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq327 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op y (M.op x y)) x))) := by
    intro X0
    first
    | exact superpose eq183 eq34
    | exact resolve eq34 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq183
  have eq357 : ∀ X0 : G, (k X0 (σ (M.op (M.op y (M.op x y)) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq327 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq327
    | exact resolve eq327 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq396 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq723 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq724 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq853 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq179 X1 X2 (σ X0)
       grind)
    | exact superpose eq179 eq396
    | exact resolve eq396 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq396
  have eq870 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq853 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq853
    | exact resolve eq853 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq1255 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq723
       grind)
    | exact superpose eq723 eq39
    | exact resolve eq39 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1256 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1255
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1255
    | exact resolve eq1255 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1258 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1256
    | exact resolve eq1256 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1548 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq182
  have eq1607 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op (M.op X0 X0) (M.op X2 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq870 X1 X0 (M.op X2 X2)
       have i₂ := eq1548 X2 X0
       grind)
    | exact superpose eq1548 eq870
    | exact resolve eq870 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq1623 : ∀ X1 X2 : G, (k X1 (τ (M.op X2 X2))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq1607 x X1 X2
       have i₂ := eq1548 x (M.op X2 X2)
       grind)
    | exact superpose eq1548 eq1607
    | exact resolve eq1607 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq4120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1258 eq724
    | exact resolve eq724 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq4129 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq4120
       have r₂ := eq27
       grind)
    | exact resolve eq4120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4120
  have eq4146 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4129 eq1623
    | exact resolve eq1623 eq4129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623 eq4129
  have eq4222 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq4146
    | exact resolve eq4146 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4146
  have eq4233 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4222 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq4222 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq4222 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4222
  have eq4249 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq723
       have i₂ := eq4233 y
       grind)
    | exact superpose eq4233 eq723
    | exact resolve eq723 eq4233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq4233
  have eq4255 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4249
  have eq4280 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1548 x X0
       have i₂ := eq4255
       grind)
    | exact superpose eq4255 eq1548
    | exact resolve eq1548 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4255
  have eq4437 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4280 y
       grind)
    | exact superpose eq4280 eq18
    | (have j1 := eq4280 y
       grind)
    | exact resolve eq18 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4280
  have eq4520 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4437
  have eq4566 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4520 eq27
    | exact resolve eq27 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4570 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (σ y)) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4520 eq187
    | exact resolve eq187 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq4520
  have eq4625 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4570 X0
       have i₂ := eq1548 sF3 sF2
       grind)
    | exact superpose eq1548 eq4570
    | exact resolve eq4570 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4570
  have eq4662 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4625 eq1258
    | exact resolve eq1258 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq4625
  have eq4667 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq4662
  have eq4676 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4667
       have r₂ := eq4566
       grind)
    | exact resolve eq4667 eq4566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566 eq4667
  have eq4870 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1548 x X0
       have i₂ := eq4676
       grind)
    | exact superpose eq4676 eq1548
    | exact resolve eq1548 eq4676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4676
  have eq4969 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4870 y
       grind)
    | exact superpose eq4870 eq18
    | (have j1 := eq4870 y
       grind)
    | exact resolve eq18 eq4870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4870
  have eq5052 : y = (M.op x y) := by grind
  clear eq4969
  have eq5099 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5052
       grind)
    | exact superpose eq5052 eq24
    | exact resolve eq24 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq5113 : ∀ X0 : G, (k X0 (σ (M.op (M.op (M.op x y) (M.op x y)) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq5052
       grind)
    | exact superpose eq5052 eq357
    | exact resolve eq357 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq5052
  have eq5161 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5113 X0
       have i₂ := eq1548 sF0 x
       grind)
    | exact superpose eq1548 eq5113
    | exact resolve eq5113 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5113
  have eq5181 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5161 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5161
    | (have j0 := eq5161 X0
       grind)
    | exact resolve eq5161 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5161
  have eq5187 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5099 eq20
    | exact resolve eq20 eq5099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5099
  have eq5981 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5181 eq770
    | (have j0 := eq770 (σ x)
       grind)
    | (have r₁ := eq770 (σ x)
       have r₂ := eq5181 (σ x)
       grind)
    | exact resolve eq770 eq5181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq5181
  have eq6001 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5981
  have eq6027 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq6001 eq1548
    | exact resolve eq1548 eq6001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548 eq6001
  have eq6122 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6027 eq26
    | (have j1 := eq6027 (σ y)
       grind)
    | exact resolve eq26 eq6027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6027
  have eq6427 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq6122 eq27
    | exact resolve eq27 eq6122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6122
  have eq6490 : False := by grind
  exact eq6490

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pxx_pxy_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq41 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq42 (τ X0)
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq82
    | exact resolve eq82 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq82
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq10
    | exact resolve eq10 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq105 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq24 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq173 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq24
    | exact resolve eq24 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X1 X2
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq24
    | exact resolve eq24 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq463 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq157
       have i₂ := eq94 y
       grind)
    | exact superpose eq94 eq157
    | exact resolve eq157 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq157
  have eq489 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq463
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq463
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq463 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq463
  have eq490 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq489
  have eq643 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 (σ (M.op X0 X0)) x X1
       have i₂ := eq173 X0 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq173 eq105
    | exact resolve eq105 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq173
  have eq915 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq106 X0 X1 x
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq9103 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) (M.op X0 X0))) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq915 (σ y) X0 (σ x)
       have i₂ := eq490
       grind)
    | exact superpose eq490 eq915
    | exact resolve eq915 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq9137 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq915 X1 (τ X0) X2
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq915
    | exact resolve eq915 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq915
  have eq9344 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq9103 x
       have i₂ := eq174 y (σ y) x
       grind)
    | exact superpose eq174 eq9103
    | exact resolve eq9103 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq9103
  have eq44694 : y = (τ (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9344
       grind)
    | exact superpose eq9344 eq10
    | exact resolve eq10 eq9344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9344
  have eq44757 : x = y ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq44694
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq44694
    | exact resolve eq44694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44694
  have eq44760 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44757
       grind)
    | exact superpose eq44757 eq16
    | exact resolve eq16 eq44757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44757
  have eq44761 : (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq44760
       have r₂ := eq643 x (σ x)
       grind)
    | exact resolve eq44760 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44760
  have eq44933 : ∀ X0 : G, y = (M.op (M.op y x) (M.op y (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9137 X0 y y
       have i₂ := eq44761
       grind)
    | exact superpose eq44761 eq9137
    | exact resolve eq9137 eq44761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44761
  have eq44935 : x = y := by
    first
    | (have i₁ := eq44933 x
       have i₂ := eq9137 x y x
       grind)
    | exact superpose eq9137 eq44933
    | exact resolve eq44933 eq9137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9137 eq44933
  have eq44943 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44935
       grind)
    | exact superpose eq44935 eq16
    | exact resolve eq16 eq44935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44935
  have eq44945 : False := by grind
  exact eq44945

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq39 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq44 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq44
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq52
  have eq137 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq141 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       have j1 := eq55 X1 X0
       grind)
    | (have r₁ := eq137 X1 X0
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq137 X1 X1
       have r₂ := eq55 X1 X1
       grind)
    | exact resolve eq137 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq137
  have eq304 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq141 (σ X1) (σ X0)
       grind)
    | exact superpose eq141 eq15
    | exact resolve eq15 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq141 X1 X0
       grind)
    | exact superpose eq141 eq304
    | exact resolve eq304 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq304
  have eq314 : False := by grind
  exact eq314

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
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
  have eq42 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq42 (σ X0)
       grind)
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq56
    | exact resolve eq56 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq56
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq79
    | (have j0 := eq79 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq79 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq226 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq156
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq156
    | (have j1 := eq79 (σ x) (σ y)
       grind)
    | (have r₁ := eq156
       have r₂ := eq79 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq156
       have r₂ := eq79 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq156 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq156
  have eq229 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq226
  have eq230 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq229
       grind)
    | exact superpose eq229 eq16
    | exact resolve eq16 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq231 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq230
       have r₂ := eq65 x
       grind)
    | exact resolve eq230 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq267 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq231
       grind)
    | exact superpose eq231 eq10
    | exact resolve eq10 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq284 : x = y := by
    first
    | (have i₁ := eq267
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq267
    | exact resolve eq267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq328 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq284
       grind)
    | exact superpose eq284 eq16
    | exact resolve eq16 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq329 : False := by grind
  exact eq329

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxy_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq71 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq10
    | exact resolve eq10 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq50
    | exact resolve eq50 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq76 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq75
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq75
    | exact resolve eq75 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq73
    | exact resolve eq73 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq68
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq129 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq71 sF1
       grind)
    | exact superpose eq71 eq126
    | exact resolve eq126 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq129
       have i₂ := eq71 sF0
       grind)
    | exact superpose eq71 eq129
    | exact resolve eq129 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq129
  have eq148 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq131 eq37
    | exact resolve eq37 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq131
  have eq473 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq52
    | exact resolve eq52 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq474 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq52 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X1
       have i₂ := eq52 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 x (M.op X0 X0) X2
       have i₂ := eq52 x (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq52
  have eq1114 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq477 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq477 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq477 eq13
    | (have j0 := eq13 X2 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq1143 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq1114 X0 x X2
       grind)
    | (have r₁ := eq1114 x X0 X2
       have r₂ := eq474 X0 x x
       grind)
    | (have r₁ := eq1114 (M.op X0 X0) (M.op X0 X0) X2
       have r₂ := eq474 X0 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq1114 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq1114
  have eq1420 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq587 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq587
    | (have j0 := eq587 X0 x y
       grind)
    | exact resolve eq587 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq2247 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op X0 X0)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq580 x (σ (M.op X0 X0))
       have i₂ := eq473 X0 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq473 eq580
    | exact resolve eq580 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq580
  have eq15920 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq148
       have i₂ := eq1143 sF1 sF3
       grind)
    | exact superpose eq1143 eq148
    | exact resolve eq148 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq15921 : (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op y (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq15920
       have i₂ := eq1143 sF0 y
       grind)
    | exact superpose eq1143 eq15920
    | exact resolve eq15920 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq15920
  have eq25032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq25033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq25032
    | exact resolve eq25032 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25032
  have eq25038 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq25033
       have r₂ := eq28
       grind)
    | exact resolve eq25033 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25033
  have eq25042 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq25038 eq76
    | exact resolve eq76 eq25038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25038
  have eq25204 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq25042
    | exact resolve eq25042 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25042
  have eq25205 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25204
  have eq25302 : y = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1420 x
       have i₂ := eq25205
       grind)
    | exact superpose eq25205 eq1420
    | exact resolve eq1420 eq25205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq25327 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2247 x
       have i₂ := eq25205
       grind)
    | exact superpose eq25205 eq2247
    | exact resolve eq2247 eq25205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247 eq25205
  have eq25358 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25327
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25327
    | exact resolve eq25327 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25327
  have eq152302 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25302 eq476
    | exact resolve eq476 eq25302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25302
  have eq152593 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25358 eq476
    | exact resolve eq476 eq25358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq25358
  have eq199787 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15921
       have i₂ := eq152302 sF0
       grind)
    | exact superpose eq152302 eq15921
    | exact resolve eq15921 eq152302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15921 eq152302
  have eq199870 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq199787
    | exact resolve eq199787 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199787
  have eq229708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq199870 eq152593
    | exact resolve eq152593 eq199870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152593 eq199870
  have eq229745 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq229708
  have eq229761 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq229745
       have r₂ := eq28
       grind)
    | exact resolve eq229745 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229745
  have eq230116 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq229761 eq30
    | exact resolve eq30 eq229761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq229761
  have eq230187 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq230116
    | exact resolve eq230116 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq230116
  have eq230188 : x = y := by grind
  clear eq230187
  have eq230197 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq230188
       grind)
    | exact superpose eq230188 eq19
    | exact resolve eq19 eq230188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq230198 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq230188
       grind)
    | exact superpose eq230188 eq25
    | exact resolve eq25 eq230188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq230188
  have eq230410 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq230198
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq230198
    | exact resolve eq230198 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq230198
  have eq230439 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq230410 eq27
    | exact resolve eq27 eq230410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq230410
  have eq231547 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq230439 eq76
    | exact resolve eq76 eq230439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq230439
  have eq232014 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq231547
       have i₂ := eq230197
       grind)
    | exact superpose eq230197 eq231547
    | exact resolve eq231547 eq230197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230197 eq231547
  have eq232016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq232014 eq15
    | exact resolve eq15 eq232014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232014
  have eq232224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq232016
    | exact resolve eq232016 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq232016
  have eq232288 : False := by grind
  exact eq232288

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq42 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq42 (σ X0)
       grind)
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq56
    | exact resolve eq56 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq56
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq79
    | (have j0 := eq79 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq79 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 y x
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq226 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq156
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq156
    | (have j1 := eq79 (σ x) (σ y)
       grind)
    | (have r₁ := eq156
       have r₂ := eq79 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq156
       have r₂ := eq79 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq156 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq156
  have eq229 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq226
  have eq230 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq229
       grind)
    | exact superpose eq229 eq16
    | exact resolve eq16 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq231 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq230
       have r₂ := eq65 x
       grind)
    | exact resolve eq230 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq267 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq231
       grind)
    | exact superpose eq231 eq10
    | exact resolve eq10 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq284 : x = y := by
    first
    | (have i₁ := eq267
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq267
    | exact resolve eq267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq328 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq284
       grind)
    | exact superpose eq284 eq16
    | exact resolve eq16 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq329 : False := by grind
  exact eq329

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_x_pyy_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq29 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq55 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq56 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq10
    | exact resolve eq10 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq100
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq219 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq60 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq60 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq60 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq60 x (M.op X0 X0) X0
       have i₂ := eq219 (M.op X0 X0) x X2
       grind)
    | (have i₁ := eq60 (M.op X2 X2) (M.op X2 X2) X2
       have i₂ := eq219 X0 x (M.op (M.op X2 X2) (M.op X2 X2))
       grind)
    | exact superpose eq219 eq60
    | exact resolve eq60 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq288 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X2)) X1 X2
       have i₂ := eq246 X0 (M.op X1 (M.op X2 X2))
       grind)
    | (have i₁ := eq9 (M.op X1 (M.op X2 X2)) X1 X2
       have i₂ := eq246 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact superpose eq246 eq9
    | exact resolve eq9 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq55
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq141
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq141 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq56
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq47
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq397 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq393
    | exact resolve eq393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq399 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq397
    | exact resolve eq397 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq441 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq223 X0 X1 x
       grind)
    | exact superpose eq223 eq9
    | exact resolve eq9 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X1 (M.op (M.op X2 X2) X0) x
       have i₂ := eq224 X2 x X0
       grind)
    | exact superpose eq224 eq60
    | exact resolve eq60 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op (M.op X1 X1) X0)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X1) X0) x
       have i₂ := eq224 X1 x X0
       grind)
    | exact superpose eq224 eq9
    | exact resolve eq9 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq441 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq441
    | (have j0 := eq441 x X0 y
       grind)
    | exact resolve eq441 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq27 eq441
    | (have j0 := eq441 (σ x) X0 (σ y)
       grind)
    | exact resolve eq441 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : ∀ X0 X1 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op (M.op X1 X1) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq530 eq501
    | exact resolve eq501 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq761 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) (M.op (M.op X1 X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq531 eq501
    | exact resolve eq501 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq803 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq500 (M.op (M.op X1 X1) X0) X0 X2
       have i₂ := eq501 X0 X1 X0
       grind)
    | exact superpose eq501 eq500
    | exact resolve eq500 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2266 : ∀ X0 X2 : G, (M.op (M.op (M.op y (M.op (M.op X0 X0) (M.op x y))) X2) x) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 x x
       have i₂ := eq759 x X0
       grind)
    | exact superpose eq759 eq9
    | exact resolve eq9 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq2328 : ∀ X0 X2 : G, (M.op (M.op (M.op (σ y) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) X2) (σ x)) = X2 := by
    intro X0 X2
    first
    | exact superpose eq761 eq9
    | exact resolve eq9 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq3339 : ∀ X0 X1 : G, (M.op y (M.op X1 X1)) = (M.op (M.op (M.op X0 X0) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2266 X0 (M.op y (M.op X1 X1))
       have i₂ := eq441 y X1 (M.op (M.op X0 X0) sF0)
       grind)
    | exact superpose eq441 eq2266
    | exact resolve eq2266 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq3721 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 X1)) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2328 X0 (M.op sF3 (M.op X1 X1))
       have i₂ := eq441 sF3 X1 (M.op (M.op X0 X0) sF4)
       grind)
    | exact superpose eq441 eq2328
    | exact resolve eq2328 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq2328
  have eq4523 : ∀ X0 X2 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) x) (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq223 y x X2
       have i₂ := eq3339 X0 x
       grind)
    | exact superpose eq3339 eq223
    | exact resolve eq223 eq3339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3339
  have eq4664 : ∀ X0 X2 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) (M.op X2 X2)) := by
    intro X0 X2
    first
    | exact superpose eq3721 eq223
    | exact resolve eq223 eq3721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq3721
  have eq6211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq399
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq399
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq399 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq6225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq6211
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq6211
    | exact resolve eq6211 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6211
  have eq6228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq6225
    | exact resolve eq6225 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6225
  have eq6229 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq6228
       have r₂ := eq28
       grind)
    | exact resolve eq6228 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6228
  have eq6230 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6229
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq6229
    | exact resolve eq6229 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6229
  have eq6355 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (M.op X0 X0)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6230 eq4664
    | exact resolve eq4664 eq6230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4664 eq6230
  have eq6360 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6355 x
       have i₂ := eq224 sF4 x sF2
       grind)
    | exact superpose eq224 eq6355
    | exact resolve eq6355 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6355
  have eq6361 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6360
  have eq6504 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4523 y X0
       have i₂ := eq6361
       grind)
    | exact superpose eq6361 eq4523
    | exact resolve eq4523 eq6361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4523 eq6361
  have eq6515 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6504 x
       have i₂ := eq224 sF0 x x
       grind)
    | exact superpose eq224 eq6504
    | exact resolve eq6504 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq6504
  have eq6516 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6515
  have eq6878 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq6516 eq44
    | exact resolve eq44 eq6516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq6516
  have eq6913 : x = y ∨ x = y := by
    first
    | exact superpose eq43 eq6878
    | exact resolve eq6878 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6878
  have eq6914 : x = y := by grind
  clear eq6913
  have eq6918 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq6914
       grind)
    | exact superpose eq6914 eq19
    | exact resolve eq19 eq6914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq6919 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq6914
       grind)
    | exact superpose eq6914 eq25
    | exact resolve eq25 eq6914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq6914
  have eq7357 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq6919
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6919
    | exact resolve eq6919 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6919
  have eq7392 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7357 eq27
    | exact resolve eq27 eq7357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7357
  have eq7844 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq60 x X0 X1
       have i₂ := eq6918
       grind)
    | exact superpose eq6918 eq60
    | exact resolve eq60 eq6918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq7854 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq246 x X0
       have i₂ := eq6918
       grind)
    | exact superpose eq6918 eq246
    | exact resolve eq246 eq6918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq7855 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X1 X0 x
       have i₂ := eq6918
       grind)
    | exact superpose eq6918 eq288
    | exact resolve eq288 eq6918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq7860 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq500 X0 x X1
       have i₂ := eq6918
       grind)
    | exact superpose eq6918 eq500
    | exact resolve eq500 eq6918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq7861 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq501 X0 x X1
       have i₂ := eq6918
       grind)
    | exact superpose eq6918 eq501
    | exact resolve eq501 eq6918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq7864 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op x y) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq803 X1 x X0
       have i₂ := eq6918
       grind)
    | exact superpose eq6918 eq803
    | exact resolve eq803 eq6918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq6918
  have eq8084 : ∀ X1 : G, (M.op (M.op x y) (M.op (M.op x y) X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq7864 X1 X1
       have i₂ := eq7860 (M.op sF0 X1) X1
       grind)
    | exact superpose eq7860 eq7864
    | exact resolve eq7864 eq7860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7864
  have eq8258 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq7855 X0 x
       have i₂ := eq7860 X0 x
       grind)
    | exact superpose eq7860 eq7855
    | exact resolve eq7855 eq7860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7855 eq7860
  have eq8261 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op x y) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq7854 X1
       grind)
    | exact superpose eq7854 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq7854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8267 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op x y) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq381 X0 X1
       have i₂ := eq7854 X1
       grind)
    | exact superpose eq7854 eq381
    | (have j0 := eq381 X0 X1
       grind)
    | exact resolve eq381 eq7854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq8269 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op x y) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 X1
       have i₂ := eq7854 X1
       grind)
    | exact superpose eq7854 eq387
    | (have j0 := eq387 X0 X1
       grind)
    | exact resolve eq387 eq7854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq8338 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op x y) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq7854 (τ X1)
       grind)
    | exact superpose eq7854 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq7854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq8364 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7392
       have i₂ := eq7854 sF2
       grind)
    | exact superpose eq7854 eq7392
    | exact resolve eq7392 eq7854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7392
  have eq8371 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7844 X0 x
       have i₂ := eq7854 x
       grind)
    | exact superpose eq7854 eq7844
    | exact resolve eq7844 eq7854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7844 eq7854
  have eq8744 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq8364 eq28
    | exact resolve eq28 eq8364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq8364
  have eq12993 : ∀ X0 : G, (τ X0) = (k (τ (M.op x y)) (τ (M.op X0 (M.op x y)))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq8371 eq8267
    | (have j0 := eq8267 X0 (M.op x y)
       grind)
    | exact resolve eq8267 eq8371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8371
  have eq13561 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (M.op x y) (τ X0))) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8258 eq8269
    | (have j0 := eq8269 X0 (M.op x y)
       grind)
    | exact resolve eq8269 eq8258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8269
  have eq13629 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (M.op x y) (τ X0))) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq13561
    | (have j0 := eq13561 X0
       grind)
    | exact resolve eq13561 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13561
  have eq15125 : ∀ X0 : G, (τ X0) = (k (τ (M.op x y)) (k (τ X0) (τ (M.op x y)))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq12993 X0
       have i₂ := eq8267 X0 sF0
       grind)
    | exact superpose eq8267 eq12993
    | (have j0 := eq12993 X0
       have j1 := eq8267 X0 (M.op x y)
       grind)
    | exact resolve eq12993 eq8267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8267 eq12993
  have eq15143 : ∀ X0 : G, (τ X0) = (k (τ (M.op x y)) (k (τ X0) (τ (M.op x y)))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq15125 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15125
  have eq62535 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13629 eq8338
    | (have j0 := eq8338 (M.op x y) X0
       have j1 := eq13629 X0
       grind)
    | exact resolve eq8338 eq13629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8338 eq13629
  have eq62589 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq62535 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62535
  have eq62595 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq62589
    | (have j0 := eq62589 X0
       grind)
    | exact resolve eq62589 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62589
  have eq62648 : ∀ X0 : G, (τ X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq62595 eq7861
    | (have j1 := eq62595 X0
       grind)
    | exact resolve eq7861 eq62595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62595
  have eq62656 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq62648 X0
       have i₂ := eq8084 (M.op sF0 (M.op sF0 sF0))
       grind)
    | exact superpose eq8084 eq62648
    | (have j0 := eq62648 X0
       grind)
    | exact resolve eq62648 eq8084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62648
  have eq62657 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq62656 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62656
  have eq62697 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq11 X0
       have i₂ := eq62657 X0
       grind)
    | exact superpose eq62657 eq11
    | (have j1 := eq62657 X0
       grind)
    | exact resolve eq11 eq62657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62698 : ∀ X0 X1 : G, (σ (k X0 (M.op x y))) = (k (σ X0) X1) ∨ (k (σ (M.op x y)) X1) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X0
       have i₂ := eq62657 X1
       grind)
    | exact superpose eq62657 eq55
    | (have j1 := eq62657 X1
       grind)
    | exact resolve eq55 eq62657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62657
  have eq62840 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq62697
    | (have j0 := eq62697 X0
       grind)
    | exact resolve eq62697 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62697
  have eq87969 : ∀ X0 X1 : G, (k X0 X1) = (σ (k (τ X0) (M.op x y))) ∨ (k (σ (M.op x y)) X1) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq62698 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62698
    | (have j0 := eq62698 X0 X1
       grind)
    | exact resolve eq62698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62698
  have eq88500 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (σ (M.op x y))) ∨ (k (σ (M.op x y)) X1) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq87969 X0 X1
       have i₂ := eq56 X0 sF0
       grind)
    | exact superpose eq56 eq87969
    | (have j0 := eq87969 X0 X1
       grind)
    | exact resolve eq87969 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87969
  have eq88558 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (σ (M.op x y))) ∨ (k (σ (M.op x y)) X1) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq21 eq88500
    | (have j0 := eq88500 X0 X1
       grind)
    | exact resolve eq88500 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88500
  have eq89819 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) ≠ (k X0 (σ (M.op x y))) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq88558 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89820 : ∀ X0 : G, (k X0 X0) ≠ (k (σ (M.op x y)) X0) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq88558 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89827 : ∀ X0 : G, (k (σ (M.op x y)) X0) ≠ X0 ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    grind
  clear eq89820
  have eq89828 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    grind
  clear eq89819
  have eq90475 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) ≠ X0 ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ (M.op x y))) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq89827 x
       have i₂ := eq88558 sF1 x
       grind)
    | (have i₁ := eq89827 (σ (M.op x y))
       have i₂ := eq88558 sF1 x
       grind)
    | exact superpose eq88558 eq89827
    | (have j0 := eq89827 X0
       have j1 := eq88558 X0 X0
       grind)
    | (have r₁ := eq89827 (k (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq88558 (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq89827 eq88558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88558 eq89827
  have eq90508 : ∀ X0 : G, (σ (M.op x y)) ≠ X0 ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ (M.op x y))) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    grind
  clear eq90475
  have eq90521 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ (M.op x y))) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq90508 X0
       have j1 := eq62840 X0
       grind)
    | (have r₁ := eq90508 X0
       have r₂ := eq62840 X0
       grind)
    | (have r₁ := eq90508 (σ (M.op x y))
       have r₂ := eq62840 (σ (M.op x y))
       grind)
    | exact resolve eq90508 eq62840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62840 eq90508
  have eq90528 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    grind
  clear eq90521
  have eq90530 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq90528 X0
       have j1 := eq89828 X0
       grind)
    | (have r₁ := eq90528 X0
       have r₂ := eq89828 X0
       grind)
    | exact resolve eq90528 eq89828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89828 eq90528
  have eq91373 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq90530 eq31
    | exact resolve eq31 eq90530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq92447 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq29 eq91373
    | exact resolve eq91373 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq91373
  have eq97272 : ∀ X0 X1 : G, (k (σ (k X0 (M.op x y))) X1) = (σ (k (k (M.op x y) X0) (τ X1))) := by
    intro X0 X1
    first
    | exact superpose eq92447 eq55
    | exact resolve eq55 eq92447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq97282 : ∀ X0 X1 X2 : G, (k (σ X1) (k X2 (σ (k X0 (M.op x y))))) = (σ (k X1 (k (τ X2) (k (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq92447 eq123
    | exact resolve eq123 eq92447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97333 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (σ (k (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq92447 eq10
    | exact resolve eq10 eq92447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92447
  have eq97426 : ∀ X0 : G, (k (M.op x y) X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq97333 X0
       have i₂ := eq10 (k sF0 X0)
       grind)
    | exact superpose eq10 eq97333
    | exact resolve eq97333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97333
  have eq100764 : ∀ X0 X1 : G, (σ (k (k (M.op x y) (τ X0)) (τ X1))) = (k (k X0 (σ (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97272 (τ X0) X1
       have i₂ := eq56 X0 sF0
       grind)
    | exact superpose eq56 eq97272
    | exact resolve eq97272 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq101049 : ∀ X0 X1 : G, (k (k (M.op x y) X0) (τ X1)) = (τ (k (σ (k X0 (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq97272 eq10
    | exact resolve eq10 eq97272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97272
  have eq101099 : ∀ X0 X1 : G, (k (k (M.op x y) X0) (τ X1)) = (k (τ (σ (k X0 (M.op x y)))) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101049 X0 X1
       have i₂ := eq141 (σ (k X0 sF0)) X1
       grind)
    | exact superpose eq141 eq101049
    | exact resolve eq101049 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101049
  have eq101275 : ∀ X0 X1 : G, (σ (k (k (M.op x y) (τ X0)) (τ X1))) = (k (k X0 (σ (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq21 eq100764
    | (have j0 := eq100764 X0 X1
       grind)
    | exact resolve eq100764 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100764
  have eq101285 : ∀ X0 X1 : G, (k (k X0 (M.op x y)) (τ X1)) = (k (k (M.op x y) X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101099 X0 X1
       have i₂ := eq10 (k X0 sF0)
       grind)
    | exact superpose eq10 eq101099
    | exact resolve eq101099 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101099
  have eq101400 : ∀ X0 X1 : G, (k (k X0 (σ (M.op x y))) X1) = (k (k (σ (M.op x y)) X0) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq101275 X1 X1
       have i₂ := eq101 sF0 X1 (τ X1)
       grind)
    | exact superpose eq101 eq101275
    | exact resolve eq101275 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq101275
  have eq101472 : ∀ X0 X1 : G, (k (k (σ (M.op x y)) X0) X1) = (k (k X0 (σ (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq101400 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq101400
    | exact resolve eq101400 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101400
  have eq101492 : ∀ X0 X1 : G, (k (k (σ (M.op x y)) X0) X1) = (k (k X0 (σ (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq21 eq101472
    | (have j0 := eq101472 X0 X1
       grind)
    | exact resolve eq101472 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101472
  have eq103448 : ∀ X0 : G, (k (k (σ (M.op x y)) X0) (M.op x y)) = (k (M.op x y) (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq101492 eq97426
    | exact resolve eq97426 eq101492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103462 : ∀ X0 : G, (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq101492 eq90530
    | exact resolve eq90530 eq101492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103465 : ∀ X0 : G, (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) = (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq90530 eq103462
    | exact resolve eq103462 eq90530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90530 eq103462
  have eq103478 : ∀ X0 : G, (k (M.op x y) (k (σ (M.op x y)) X0)) = (k (M.op x y) (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq97426 eq103448
    | exact resolve eq103448 eq97426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103448
  have eq109178 : ∀ X0 X1 : G, (k (k (M.op x y) X1) X0) = (k (k X1 (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq101285 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101285
    | exact resolve eq101285 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101285
  have eq109815 : ∀ X0 X1 : G, (k (k (k (M.op x y) X0) (σ (M.op x y))) X1) = (k (k (σ (M.op x y)) (k X0 (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq109178 eq101492
    | exact resolve eq101492 eq109178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109821 : ∀ X0 : G, (k (M.op x y) (k (k (M.op x y) X0) (σ (M.op x y)))) = (k (M.op x y) (k (σ (M.op x y)) (k X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq109178 eq103478
    | exact resolve eq103478 eq109178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109178
  have eq109822 : ∀ X0 : G, (k (M.op x y) (k (σ (M.op x y)) (k (M.op x y) X0))) = (k (M.op x y) (k (σ (M.op x y)) (k X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq103478 eq109821
    | exact resolve eq109821 eq103478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103478 eq109821
  have eq109828 : ∀ X0 X1 : G, (k (k (σ (M.op x y)) (k (M.op x y) X0)) X1) = (k (k (σ (M.op x y)) (k X0 (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq101492 eq109815
    | exact resolve eq109815 eq101492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101492 eq109815
  have eq199136 : ∀ X0 X1 X2 : G, (k X0 (k (τ X1) (k (M.op x y) X2))) = (τ (k (σ X0) (k X1 (σ (k X2 (M.op x y)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq97282 eq10
    | exact resolve eq10 eq97282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97282
  have eq199140 : ∀ X0 X1 X2 : G, (k X0 (k (τ X1) (k (M.op x y) X2))) = (k (τ (σ X0)) (τ (k X1 (σ (k X2 (M.op x y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199136 X0 X1 X2
       have i₂ := eq141 (σ X0) (k X1 (σ (k X2 sF0)))
       grind)
    | exact superpose eq141 eq199136
    | exact resolve eq199136 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199136
  have eq199206 : ∀ X0 X1 X2 : G, (k X0 (k (τ X1) (k (M.op x y) X2))) = (k (τ (σ X0)) (k (τ X1) (τ (σ (k X2 (M.op x y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199140 X0 X0 X2
       have i₂ := eq141 X0 (σ (k X2 sF0))
       grind)
    | exact superpose eq141 eq199140
    | exact resolve eq199140 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq199140
  have eq199236 : ∀ X0 X1 X2 : G, (k X0 (k (τ X1) (k (M.op x y) X2))) = (k (τ (σ X0)) (k (τ X1) (k X2 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199206 X0 X1 X2
       have i₂ := eq10 (k X2 sF0)
       grind)
    | exact superpose eq10 eq199206
    | exact resolve eq199206 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199206
  have eq199244 : ∀ X0 X1 X2 : G, (k X0 (k (τ X1) (k (M.op x y) X2))) = (k X0 (k (τ X1) (k X2 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199236 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq199236
    | exact resolve eq199236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199236
  have eq258789 : ∀ X0 X1 X2 : G, (k X1 (k X0 (k (M.op x y) X2))) = (k X1 (k X0 (k X2 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199244 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq199244
    | exact resolve eq199244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199244
  have eq259197 : ∀ X0 X1 : G, (k X0 (k (M.op x y) X1)) = (k (k X0 (k (M.op x y) X1)) (k X0 (k X1 (M.op x y)))) := by
    intro X0 X1
    grind
  have eq259311 : ∀ X0 X1 : G, (k X0 (k X1 (M.op x y))) = (k (k X0 (k X1 (M.op x y))) (k X0 (k (M.op x y) X1))) := by
    intro X0 X1
    grind
  clear eq258789
  have eq436900 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ (M.op x y))) (k X0 (σ (τ (M.op x y))))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq15143 eq123
    | (have j1 := eq15143 X0
       grind)
    | exact resolve eq123 eq15143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15143
  have eq436908 : ∀ X0 : G, (σ (τ X0)) = (k (M.op x y) (k X0 (M.op x y))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq436900 X0
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq436900
    | (have j0 := eq436900 X0
       grind)
    | exact resolve eq436900 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436900
  have eq436918 : ∀ X0 : G, (k (M.op x y) (k X0 (M.op x y))) = X0 ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq436908 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq436908
    | (have j0 := eq436908 X0
       grind)
    | exact resolve eq436908 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436908
  have eq437025 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq436918 eq123
    | (have j1 := eq436918 (τ X0)
       grind)
    | exact resolve eq123 eq436918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq436918
  have eq437069 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq437025
    | (have j0 := eq437025 X0
       grind)
    | exact resolve eq437025 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437025
  have eq437091 : ∀ X0 : G, (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq437069 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq437069
    | (have j0 := eq437069 X0
       grind)
    | exact resolve eq437069 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437069
  have eq437098 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8258 eq437091
    | (have j0 := eq437091 X0
       grind)
    | exact resolve eq437091 eq8258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8258 eq437091
  have eq437496 : ∀ X0 : G, (τ X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq437098 eq7861
    | (have j1 := eq437098 X0
       grind)
    | exact resolve eq7861 eq437098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437098
  have eq437499 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq437496 X0
       have i₂ := eq8084 (M.op sF0 (M.op sF0 sF0))
       grind)
    | exact superpose eq8084 eq437496
    | (have j0 := eq437496 X0
       grind)
    | exact resolve eq437496 eq8084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437496
  have eq437500 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq437499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437499
  have eq437518 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0
       have i₂ := eq437500 X0
       grind)
    | exact superpose eq437500 eq11
    | (have j1 := eq437500 X0
       grind)
    | exact resolve eq11 eq437500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437500
  have eq437733 : ∀ X0 : G, (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq437518
    | (have j0 := eq437518 X0
       grind)
    | exact resolve eq437518 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq437518
  have eq438159 : (M.op x y) = (k (M.op x y) (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y)))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq437733 eq259197
    | (have j1 := eq437733 (M.op x y)
       grind)
    | exact resolve eq259197 eq437733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259197
  have eq438160 : (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) = (k (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq437733 eq259311
    | (have j1 := eq437733 (M.op x y)
       grind)
    | exact resolve eq259311 eq437733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259311 eq437733
  have eq438178 : (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) = (k (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) (M.op x y)) := by
    first
    | (have r₁ := eq438160
       have r₂ := eq8744
       grind)
    | exact resolve eq438160 eq8744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438160
  have eq438179 : (M.op x y) = (k (M.op x y) (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y)))) := by
    first
    | (have r₁ := eq438159
       have r₂ := eq8744
       grind)
    | exact resolve eq438159 eq8744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438159
  have eq438468 : (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) = (k (k (σ (M.op x y)) (k (M.op x y) (σ (M.op x y)))) (M.op x y)) := by
    first
    | exact superpose eq109828 eq438178
    | exact resolve eq438178 eq109828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109828 eq438178
  have eq438469 : (M.op x y) = (k (M.op x y) (k (σ (M.op x y)) (k (M.op x y) (σ (M.op x y))))) := by
    first
    | exact superpose eq109822 eq438179
    | exact resolve eq438179 eq109822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109822 eq438179
  have eq438562 : (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) = (k (M.op x y) (k (σ (M.op x y)) (k (M.op x y) (σ (M.op x y))))) := by
    first
    | exact superpose eq97426 eq438468
    | exact resolve eq438468 eq97426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97426 eq438468
  have eq438630 : (M.op x y) = (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq438469 eq438562
    | exact resolve eq438562 eq438469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438469 eq438562
  have eq438636 : (M.op x y) = (k (σ (M.op x y)) (k (M.op x y) (σ (M.op x y)))) := by
    first
    | exact superpose eq103465 eq438630
    | exact resolve eq438630 eq103465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103465 eq438630
  have eq438945 : (M.op x y) = (M.op (σ (M.op x y)) (k (M.op x y) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (k (M.op x y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq438636 eq8261
    | (have j0 := eq8261 (σ (M.op x y)) (k (M.op x y) (σ (M.op x y)))
       grind)
    | exact resolve eq8261 eq438636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8261
  have eq438952 : (M.op x y) = (M.op (σ (M.op x y)) (k (M.op x y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by grind
  clear eq438945
  have eq450525 : (k (M.op x y) (σ (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq438952 eq7861
    | exact resolve eq7861 eq438952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7861 eq438952
  have eq450531 : (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq450525
       have i₂ := eq8084 (M.op sF0 (M.op sF0 sF1))
       grind)
    | exact superpose eq8084 eq450525
    | exact resolve eq450525 eq8084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8084 eq450525
  have eq450532 : (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by grind
  clear eq450531
  have eq452003 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq450532 eq438636
    | exact resolve eq438636 eq450532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438636 eq450532
  have eq452032 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq452003
  have eq452182 : False := by grind
  exact eq452182

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 X2 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq25 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ (M.op X0 X0)) (M.op X1 X1)
       have i₂ := eq56 X0 (M.op X1 X1) (σ (M.op X0 X0))
       grind)
    | exact superpose eq56 eq62
    | exact resolve eq62 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq62
  have eq3575 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq16
    | (have j1 := eq94 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq94 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq94 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq94 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3592 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3575
  have eq3719 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3592
       grind)
    | exact superpose eq3592 eq16
    | exact resolve eq16 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3725 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3592
       grind)
    | exact superpose eq3592 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3592
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3592
       grind)
    | exact resolve eq13 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592
  have eq3726 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3725
  have eq3727 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3726
  have eq3729 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3727
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3727
    | exact resolve eq3727 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3727
  have eq13320 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3729
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq3729
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq3729 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13323 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq3729
       grind)
    | exact superpose eq3729 eq10
    | exact resolve eq10 eq3729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729
  have eq13342 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13320
  have eq13347 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13323
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13323
    | exact resolve eq13323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13323
  have eq13348 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13342
       have r₂ := eq3719
       grind)
    | exact resolve eq13342 eq3719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719 eq13342
  have eq13349 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq13347
       have r₂ := eq13 x y
       grind)
    | exact resolve eq13347 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13347
  have eq43024 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq13349
       grind)
    | exact superpose eq13349 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq13349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13349
  have eq43027 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq43024
  have eq59897 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq43027
       grind)
    | exact superpose eq43027 eq16
    | exact resolve eq16 eq43027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43027
  have eq80167 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59897
       have i₂ := eq13348
       grind)
    | exact superpose eq13348 eq59897
    | exact resolve eq59897 eq13348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13348 eq59897
  have eq80168 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq80167
  have eq80169 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq80168
  have eq112572 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq80169
       grind)
    | exact superpose eq80169 eq10
    | exact resolve eq10 eq80169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80169
  have eq112593 : x = y ∨ x = y := by
    first
    | (have i₁ := eq112572
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq112572
    | exact resolve eq112572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112572
  have eq112594 : x = y := by grind
  clear eq112593
  have eq126353 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq112594
       grind)
    | exact superpose eq112594 eq16
    | exact resolve eq16 eq112594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112594
  have eq126354 : False := by grind
  exact eq126354
