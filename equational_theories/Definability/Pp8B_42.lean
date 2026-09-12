import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  clear eq35
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
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
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
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
  have eq404 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq320 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq320
    | exact resolve eq320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
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
  have eq866 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq192
    | exact resolve eq192 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq192
  have eq886 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq866 X0
       grind)
    | exact superpose eq866 eq16
    | exact resolve eq16 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq886 (M.op X1 X0) X0
       have i₂ := eq16 X0 X1 X0
       grind)
    | exact superpose eq16 eq886
    | exact resolve eq886 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq886 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq886
    | exact resolve eq886 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq938 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq886
    | exact resolve eq886 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1008 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq921 X0 X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq921
    | exact resolve eq921 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq930 X0 X0
       grind)
    | exact superpose eq930 eq180
    | exact resolve eq180 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1379 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1008 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq1008
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1008 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1393 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq1405 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1069 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq1069
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1069 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1417 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq2147 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq638
       grind)
    | exact superpose eq638 eq40
    | exact resolve eq40 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2148 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2147
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2147
    | exact resolve eq2147 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2147
  have eq2150 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2148
    | exact resolve eq2148 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq15415 : ∀ X0 : G, (k (k (k X0 X0) X0) X0) = X0 ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k (k X0 X0) X0) X0
       have i₂ := eq1393 X0
       grind)
    | exact superpose eq1393 eq11
    | (have j0 := eq11 (k (k X0 X0) X0) X0
       have j1 := eq1393 X0
       grind)
    | exact resolve eq11 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq15449 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1417 eq15415
    | (have j0 := eq15415 X0
       have j1 := eq1417 X0
       grind)
    | exact resolve eq15415 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15415
  have eq15460 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1417 eq15449
    | (have j0 := eq15449 X0
       have j1 := eq1417 X0
       grind)
    | exact resolve eq15449 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15449
  have eq15468 : ∀ X0 : G, (M.op X0 (k (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15460 X0
       have j1 := eq665 X0
       grind)
    | (have r₁ := eq15460 X0
       have r₂ := eq665 X0
       grind)
    | exact resolve eq15460 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq15460
  have eq15471 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1417 eq15468
    | (have j0 := eq15468 X0
       have j1 := eq1417 X0
       grind)
    | exact resolve eq15468 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15468
  have eq15473 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1417 eq15471
    | (have j0 := eq15471 X0
       have j1 := eq1417 X0
       grind)
    | exact resolve eq15471 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417 eq15471
  have eq15475 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15473 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq15473 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (k (M.op x x) (M.op x x))) x
       grind)
    | (have r₁ := eq15473 x
       have r₂ := eq13 (k x x) x
       grind)
    | (have r₁ := eq15473 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq15473 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15473
  have eq16326 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq930 X0 (k X0 X0)
       have i₂ := eq15475 X0
       grind)
    | exact superpose eq15475 eq930
    | (have j1 := eq15475 X0
       grind)
    | exact resolve eq930 eq15475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16375 : y = (M.op y y) ∨ (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq580 (k y y)
       have i₂ := eq15475 y
       grind)
    | exact superpose eq15475 eq580
    | (have j1 := eq15475 y
       grind)
    | exact resolve eq580 eq15475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16386 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq728 (k sF3 sF3)
       have i₂ := eq15475 sF3
       grind)
    | exact superpose eq15475 eq728
    | (have j1 := eq15475 (σ y)
       grind)
    | exact resolve eq728 eq15475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15475
  have eq16389 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq16386
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq16386
       have r₂ := eq13 (k (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq16386 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16386
  have eq16394 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq16375
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq16375
       have r₂ := eq13 (k y y) y
       grind)
    | exact resolve eq16375 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16375
  have eq16425 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16326 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq16326 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq16326 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq16326 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq16326 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16326
  have eq16448 : ∀ X0 : G, (M.op (M.op (M.op (k (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq16389 eq886
    | exact resolve eq886 eq16389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq16538 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq866 X0
       have i₂ := eq16425 X0
       grind)
    | exact superpose eq16425 eq866
    | exact resolve eq866 eq16425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq16543 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq16425 X0
       grind)
    | exact superpose eq16425 eq16
    | exact resolve eq16 eq16425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16544 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq16425 X0
       grind)
    | exact superpose eq16425 eq16
    | exact resolve eq16 eq16425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16559 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq930 X0 X0
       have i₂ := eq16425 X0
       grind)
    | exact superpose eq16425 eq930
    | exact resolve eq930 eq16425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16567 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X1
       have i₂ := eq16425 (M.op X0 X1)
       grind)
    | exact superpose eq16425 eq16
    | exact resolve eq16 eq16425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16756 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16538 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16538
    | exact resolve eq16538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16757 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16538 (τ X0)
       have i₂ := eq404 X0 X0
       grind)
    | exact superpose eq404 eq16538
    | exact resolve eq16538 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq19872 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (k X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16544 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16544
    | exact resolve eq16544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2150 eq652
    | exact resolve eq652 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq2150
  have eq26976 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26963
       have r₂ := eq27
       grind)
    | exact resolve eq26963 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26963
  have eq26985 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16389 eq26976
    | exact resolve eq26976 eq16389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26976
  have eq26990 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq26985
       have i₂ := eq16394
       grind)
    | exact superpose eq16394 eq26985
    | exact resolve eq26985 eq16394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26985
  have eq27015 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26990 eq930
    | exact resolve eq930 eq26990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26990
  have eq27028 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16389 eq27015
    | exact resolve eq27015 eq16389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27015
  have eq27087 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27028 eq152
    | exact resolve eq152 eq27028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq27028
  have eq27155 : (σ x) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq27087
    | exact resolve eq27087 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27087
  have eq27535 : (τ (σ x)) = (k y y) ∨ y = (k y y) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27155 eq115
    | exact resolve eq115 eq27155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27155
  have eq27620 : x = (k y y) ∨ y = (k y y) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq27535
    | exact resolve eq27535 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27535
  have eq27621 : y = (k y y) ∨ x = (k y y) ∨ y = (M.op y x) := by grind
  clear eq27620
  have eq27655 : (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq27621
       grind)
    | exact superpose eq27621 eq40
    | exact resolve eq40 eq27621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq27668 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq16543 y X0
       have i₂ := eq27621
       grind)
    | exact superpose eq27621 eq16543
    | exact resolve eq16543 eq27621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27669 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq16544 y X0
       have i₂ := eq27621
       grind)
    | exact superpose eq27621 eq16544
    | exact resolve eq16544 eq27621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16544 eq27621
  have eq27716 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq27668 X0
       have i₂ := eq580 X0
       grind)
    | exact superpose eq580 eq27668
    | exact resolve eq27668 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27668
  have eq27724 : (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq27655
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27655
    | exact resolve eq27655 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27655
  have eq28836 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq27724 eq16543
    | exact resolve eq16543 eq27724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16543
  have eq28886 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq728 eq28836
    | exact resolve eq28836 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq28836
  have eq29203 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (k y y) ∨ y = (M.op y x) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq27669 X0
       have i₂ := eq27716 X0
       grind)
    | exact superpose eq27716 eq27669
    | exact resolve eq27669 eq27716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29234 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op y X0) y) X1) X0) X1) = X1 ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op (M.op y X0) y) X0
       have i₂ := eq27669 X0
       grind)
    | exact superpose eq27669 eq16
    | exact resolve eq16 eq27669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27669
  have eq29257 : ∀ X0 : G, y = (M.op y x) ∨ x = (k y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq29203 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29203
  have eq29274 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq27716 eq29234
    | exact resolve eq29234 eq27716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27716 eq29234
  have eq29318 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq29257 eq29274
    | exact resolve eq29274 eq29257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29257 eq29274
  have eq32332 : ∀ X0 : G, (M.op (M.op (k (σ y) (σ y)) X0) (σ y)) = (M.op X0 (M.op (M.op (k (σ y) (σ y)) X0) (σ y))) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq16448 eq29318
    | exact resolve eq29318 eq16448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16448 eq29318
  have eq32536 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq27724 eq32332
    | exact resolve eq32332 eq27724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27724 eq32332
  have eq32586 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28886 eq32536
    | exact resolve eq32536 eq28886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28886 eq32536
  have eq32859 : y = (M.op y x) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32586 eq26
    | (have j1 := eq32586 (σ x)
       grind)
    | exact resolve eq26 eq32586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32586
  have eq32933 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq32859
       grind)
    | exact superpose eq32859 eq16
    | exact resolve eq16 eq32859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32950 : y = (M.op y y) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq930 y x
       have i₂ := eq32859
       grind)
    | exact superpose eq32859 eq930
    | exact resolve eq930 eq32859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32956 : x = (M.op (k y y) x) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16567 y x
       have i₂ := eq32859
       grind)
    | exact superpose eq32859 eq16567
    | exact resolve eq16567 eq32859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16567 eq32859
  have eq32963 : y = (k y y) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32950
       have i₂ := eq16394
       grind)
    | exact superpose eq16394 eq32950
    | exact resolve eq32950 eq16394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32950
  have eq32977 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32933 X0
       have i₂ := eq580 X0
       grind)
    | exact superpose eq580 eq32933
    | exact resolve eq32933 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq32933
  have eq36372 : ∀ X0 : G, (M.op (M.op (M.op (k y y) X0) x) X0) = X0 ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (k y y) x
       have i₂ := eq32956
       grind)
    | exact superpose eq32956 eq16
    | exact resolve eq16 eq32956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32956
  have eq36415 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32963 eq36372
    | exact resolve eq36372 eq32963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32963 eq36372
  have eq36440 : ∀ X0 : G, x = (k y y) ∨ (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32977 eq36415
    | exact resolve eq36415 eq32977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32977 eq36415
  have eq37197 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16756 y
       have i₂ := eq36440 X0
       grind)
    | exact superpose eq36440 eq16756
    | (have j1 := eq36440 X0
       grind)
    | exact resolve eq16756 eq36440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16756 eq36440
  have eq37233 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37197 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37197
    | (have j0 := eq37197 X0
       grind)
    | exact resolve eq37197 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37197
  have eq37282 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37233 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37233
    | (have j0 := eq37233 X0
       grind)
    | exact resolve eq37233 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37233
  have eq37300 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq37282
    | (have j0 := eq37282 X0
       grind)
    | exact resolve eq37282 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37282
  have eq37301 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq37300 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37300
  have eq37365 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16425 x
       have i₂ := eq37301 x
       grind)
    | exact superpose eq37301 eq16425
    | exact resolve eq16425 eq37301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37369 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 x X0
       have i₂ := eq37301 X0
       grind)
    | exact superpose eq37301 eq16
    | exact resolve eq16 eq37301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37448 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq37301 eq37369
    | exact resolve eq37369 eq37301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37301 eq37369
  have eq37559 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19872 x X0
       have i₂ := eq37365
       grind)
    | exact superpose eq37365 eq19872
    | exact resolve eq19872 eq37365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19872 eq37365
  have eq37579 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37559 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37559
    | (have j0 := eq37559 X0
       grind)
    | exact resolve eq37559 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37559
  have eq37600 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37448 eq37579
    | exact resolve eq37579 eq37448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37448 eq37579
  have eq37757 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37600 eq26
    | (have j1 := eq37600 (σ y)
       grind)
    | exact resolve eq26 eq37600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37600
  have eq37821 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq37757
  have eq37852 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq37821 eq27
    | exact resolve eq27 eq37821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq37872 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37821 eq938
    | exact resolve eq938 eq37821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq37934 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq37872 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq37872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37872
  have eq37972 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq16389 eq37934
    | exact resolve eq37934 eq16389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37934
  have eq49366 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq37972 eq90
    | exact resolve eq90 eq37972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq37972
  have eq49380 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq31 eq49366
    | exact resolve eq49366 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49366
  have eq49821 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq49380 eq921
    | exact resolve eq921 eq49380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq49822 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq49380 eq930
    | exact resolve eq930 eq49380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq49845 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq16389 eq49822
    | exact resolve eq49822 eq16389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16389 eq49822
  have eq49846 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq49821
    | exact resolve eq49821 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq49821
  have eq49871 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (k x y) := by
    first
    | exact superpose eq37821 eq49846
    | exact resolve eq49846 eq37821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37821 eq49846
  have eq51991 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x y) := by grind
  clear eq49845
  have eq52101 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (k x y) := by
    first
    | exact superpose eq49871 eq16559
    | exact resolve eq16559 eq49871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49871
  have eq52125 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k x y) := by grind
  clear eq52101
  have eq52141 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq52125 eq49380
    | exact resolve eq49380 eq52125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49380 eq52125
  have eq52188 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x y) := by grind
  clear eq52141
  have eq52203 : (σ x) = (k (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have r₁ := eq52188
       have r₂ := eq51991
       grind)
    | exact resolve eq52188 eq51991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51991 eq52188
  have eq52224 : (τ (σ x)) = (k y y) ∨ y = (k x y) := by
    first
    | exact superpose eq52203 eq115
    | exact resolve eq115 eq52203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq52272 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq52203 eq16757
    | exact resolve eq16757 eq52203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16757 eq52203
  have eq52298 : y = (M.op (τ (σ x)) y) ∨ y = (k x y) := by
    first
    | exact superpose eq31 eq52272
    | exact resolve eq52272 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq52272
  have eq52315 : y = (k x y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq52224
    | exact resolve eq52224 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52224
  have eq52323 : y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq29 eq52298
    | exact resolve eq52298 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52298
  have eq52332 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52323
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52323
    | exact resolve eq52323 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52323
  have eq52342 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq638
       have i₂ := eq52332
       grind)
    | exact superpose eq52332 eq638
    | exact resolve eq638 eq52332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq52332
  have eq52358 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq52342
  have eq52368 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq52358
       have i₂ := eq16394
       grind)
    | exact superpose eq16394 eq52358
    | exact resolve eq52358 eq16394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52358
  have eq53153 : y ≠ y ∨ x = (M.op y y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq52368
       grind)
    | exact superpose eq52368 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq52368
       grind)
    | exact resolve eq12 eq52368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52368
  have eq53189 : x = (M.op y y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq53153
  have eq53220 : x = (k y y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq53189
       have i₂ := eq16394
       grind)
    | exact superpose eq16394 eq53189
    | exact resolve eq53189 eq16394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16394 eq53189
  have eq53221 : x = (k y y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq53220
  have eq53237 : (k x x) = (k x y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53221
       have i₂ := eq16425 x
       grind)
    | exact superpose eq16425 eq53221
    | exact resolve eq53221 eq16425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16425 eq53221
  have eq53245 : y = (k x x) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52315 eq53237
    | exact resolve eq53237 eq52315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52315 eq53237
  have eq53494 : y = (M.op x y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16559 x
       have i₂ := eq53245
       grind)
    | exact superpose eq53245 eq16559
    | exact resolve eq16559 eq53245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16559 eq53245
  have eq53537 : y = (M.op x y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53494
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53494
    | exact resolve eq53494 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53494
  have eq53538 : x = (k y y) ∨ y = (M.op x y) := by grind
  clear eq53537
  have eq53595 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16538 y
       have i₂ := eq53538
       grind)
    | exact superpose eq53538 eq16538
    | exact resolve eq16538 eq53538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16538 eq53538
  have eq53638 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53595
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53595
    | exact resolve eq53595 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq53595
  have eq53639 : y = (M.op x y) := by grind
  clear eq53638
  have eq53665 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq53639
       grind)
    | exact superpose eq53639 eq24
    | exact resolve eq24 eq53639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq53639
  have eq53810 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq53665 eq20
    | exact resolve eq20 eq53665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq53665
  have eq53964 : False := by grind
  exact eq53964

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq88 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq81
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
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
  clear eq72
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq97
  have eq165 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq187 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq369 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq375 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq369 X0
       grind)
    | exact superpose eq369 eq14
    | exact resolve eq14 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq375
    | exact resolve eq375 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq375
    | exact resolve eq375 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq375
    | exact resolve eq375 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq959 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op x X0)
       have i₂ := eq845 x X0
       grind)
    | exact superpose eq845 eq54
    | exact resolve eq54 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq964 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op sF2 x)
       have i₂ := eq845 sF2 x
       grind)
    | exact superpose eq845 eq55
    | exact resolve eq55 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq845
  have eq5933 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq165 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq165
    | (have j0 := eq165 x
       grind)
    | exact resolve eq165 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq5967 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5933
  have eq5970 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5967
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5967
    | exact resolve eq5967 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5967
  have eq5986 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5970
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq5970 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5970
  have eq5991 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5986 eq50
    | exact resolve eq50 eq5986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq6116 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq187 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq187
    | (have j0 := eq187 y
       grind)
    | exact resolve eq187 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq6134 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6116
  have eq6136 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6134
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq6134
    | exact resolve eq6134 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6134
  have eq6159 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6136
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq6136 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6136
  have eq6173 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6159 eq102
    | exact resolve eq102 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq13832 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5986 eq88
    | exact resolve eq88 eq5986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq14287 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6159 eq103
    | exact resolve eq103 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq20569 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq13832
       grind)
    | exact superpose eq13832 eq16
    | exact resolve eq16 eq13832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13832
  have eq20625 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5991 eq20569
    | exact resolve eq20569 eq5991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20569
  have eq20628 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq20625
       have r₂ := eq13 x x
       grind)
    | exact resolve eq20625 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20625
  have eq20629 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20628
       grind)
    | exact superpose eq20628 eq44
    | exact resolve eq44 eq20628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq20668 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq5986 eq20629
    | exact resolve eq20629 eq5986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5986 eq20629
  have eq21430 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq14287
       grind)
    | exact superpose eq14287 eq16
    | exact resolve eq16 eq14287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14287
  have eq21490 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6173 eq21430
    | exact resolve eq21430 eq6173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21430
  have eq21493 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq21490
       have r₂ := eq13 x y
       grind)
    | exact resolve eq21490 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21490
  have eq21494 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq21493
       grind)
    | exact superpose eq21493 eq73
    | exact resolve eq73 eq21493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq21533 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq6159 eq21494
    | exact resolve eq21494 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6159 eq21494
  have eq28502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq28509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq28502
    | exact resolve eq28502 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28502
  have eq28520 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28509
       have r₂ := eq28
       grind)
    | exact resolve eq28509 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28509
  have eq28524 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28520 eq6173
    | exact resolve eq6173 eq28520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6173 eq28520
  have eq28585 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28524
       have i₂ := eq21493
       grind)
    | exact superpose eq21493 eq28524
    | exact resolve eq28524 eq21493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21493 eq28524
  have eq28594 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq28585
    | exact resolve eq28585 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28585
  have eq28595 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq28594
  have eq28598 : (τ (σ x)) = (k x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28595 eq5991
    | exact resolve eq5991 eq28595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5991 eq28595
  have eq28698 : (τ (σ x)) = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28598
       have i₂ := eq20628
       grind)
    | exact superpose eq20628 eq28598
    | exact resolve eq28598 eq20628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20628 eq28598
  have eq28707 : x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq28698
    | exact resolve eq28698 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28698
  have eq28708 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq28707
  have eq28717 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21533
       have i₂ := eq28708
       grind)
    | exact superpose eq28708 eq21533
    | exact resolve eq21533 eq28708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21533
  have eq28722 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq369 y
       have i₂ := eq28708
       grind)
    | exact superpose eq28708 eq369
    | exact resolve eq369 eq28708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28708
  have eq28762 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28722
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28722
    | exact resolve eq28722 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28722
  have eq28765 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28717
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28717
    | exact resolve eq28717 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28717
  have eq28827 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq28762
       grind)
    | exact superpose eq28762 eq51
    | exact resolve eq51 eq28762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq28844 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq959 x
       have i₂ := eq28762
       grind)
    | exact superpose eq28762 eq959
    | exact resolve eq959 eq28762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959 eq28762
  have eq28902 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq848 eq28844
    | exact resolve eq28844 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq28844
  have eq29274 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28765 eq369
    | exact resolve eq369 eq28765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq28765
  have eq29313 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq29274
    | exact resolve eq29274 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29274
  have eq29385 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20668
       have i₂ := eq29313
       grind)
    | exact superpose eq29313 eq20668
    | exact resolve eq20668 eq29313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20668 eq29313
  have eq29473 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29385
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29385
    | exact resolve eq29385 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29385
  have eq29639 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29473 eq964
    | exact resolve eq964 eq29473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq29698 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq851 eq29639
    | exact resolve eq29639 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq29639
  have eq29828 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28902 eq28827
    | exact resolve eq28827 eq28902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28827 eq28902
  have eq29864 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq29828
  have eq29865 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29864
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29864
    | exact resolve eq29864 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29864
  have eq29866 : y = (M.op x y) := by grind
  clear eq29865
  have eq29869 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29866 eq21
    | exact resolve eq21 eq29866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq29866
  have eq30049 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq29869
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29869
    | exact resolve eq29869 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29869
  have eq30090 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30049 eq27
    | exact resolve eq27 eq30049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq30094 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq30049 eq52
    | exact resolve eq52 eq30049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq31658 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29473 eq30094
    | exact resolve eq30094 eq29473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29473 eq30094
  have eq31715 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq30049 eq31658
    | exact resolve eq31658 eq30049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31658
  have eq31716 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq31715
       have r₂ := eq28
       grind)
    | exact resolve eq31715 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31715
  have eq31717 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29698 eq31716
    | exact resolve eq31716 eq29698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29698 eq31716
  have eq31754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30090 eq31717
    | exact resolve eq31717 eq30090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30090 eq31717
  have eq31755 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31754
       have r₂ := eq28
       grind)
    | exact resolve eq31754 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31754
  have eq31756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30049 eq31755
    | exact resolve eq31755 eq30049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30049 eq31755
  have eq31757 : False := by grind
  exact eq31757

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
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
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq140 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq169 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq215 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq520 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq512 X0
       grind)
    | exact superpose eq512 eq14
    | exact resolve eq14 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq703 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq705 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq704 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq871 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq520
    | exact resolve eq520 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq520
    | exact resolve eq520 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq3514 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
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
  have eq3522 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3514 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3514
    | (have j0 := eq3514 X0
       grind)
    | exact resolve eq3514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514
  have eq3528 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3522 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3522
    | (have j0 := eq3522 X0
       grind)
    | exact resolve eq3522 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522
  have eq6109 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq169 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq169
    | (have j0 := eq169 x
       grind)
    | exact resolve eq169 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq6148 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6109
  have eq6152 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6148
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6148
    | exact resolve eq6148 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6148
  have eq6169 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6152
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq6152 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6152
  have eq6174 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6169 eq49
    | exact resolve eq49 eq6169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6169
  have eq8573 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq703 x y
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq703
    | (have j0 := eq703 x y
       grind)
    | exact resolve eq703 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq8614 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8573
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8573
    | exact resolve eq8573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8573
  have eq8701 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8614
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8614
    | exact resolve eq8614 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8614
  have eq8787 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8701
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8701
    | exact resolve eq8701 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8701
  have eq8871 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq8787
    | exact resolve eq8787 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8787
  have eq8941 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8871
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8871
    | exact resolve eq8871 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8871
  have eq13602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq13603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq13602
    | exact resolve eq13602 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13602
  have eq13614 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq13603
       have r₂ := eq27
       grind)
    | exact resolve eq13603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13603
  have eq13616 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq13614
    | exact resolve eq13614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13614
  have eq13618 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq13616 eq6174
    | exact resolve eq6174 eq13616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13616
  have eq13709 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq13618
    | exact resolve eq13618 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13618
  have eq13711 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3528 x
       grind)
    | (have r₁ := eq13709
       have r₂ := eq3528 x
       grind)
    | exact resolve eq13709 eq3528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528 eq13709
  have eq14448 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq13711
       grind)
    | exact superpose eq13711 eq50
    | exact resolve eq50 eq13711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14449 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq13711
       grind)
    | exact superpose eq13711 eq53
    | exact resolve eq53 eq13711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14466 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq13711
       grind)
    | exact superpose eq13711 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq13711
       grind)
    | exact resolve eq13 eq13711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13711
  have eq14501 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14466 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14466
  have eq14525 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq871 eq14449
    | exact resolve eq14449 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14449
  have eq14563 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14525 eq14448
    | exact resolve eq14448 eq14525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14448
  have eq14599 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14563
  have eq14600 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14599
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14599
    | exact resolve eq14599 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14599
  have eq15363 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14600 eq873
    | exact resolve eq873 eq14600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14600
  have eq15377 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15363 eq6174
    | exact resolve eq6174 eq15363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6174 eq15363
  have eq15468 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq15377
    | exact resolve eq15377 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15377
  have eq16467 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq15468
       grind)
    | exact superpose eq15468 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq15468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15468
  have eq16481 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16467
  have eq17466 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq16481
       grind)
    | exact superpose eq16481 eq50
    | exact resolve eq50 eq16481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17467 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq16481
       grind)
    | exact superpose eq16481 eq53
    | exact resolve eq53 eq16481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq16481
  have eq17543 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq871 eq17467
    | exact resolve eq17467 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17467
  have eq17650 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq14501 y
       grind)
    | exact superpose eq14501 eq71
    | exact resolve eq71 eq14501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq20766 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17543 eq17466
    | exact resolve eq17466 eq17543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17466 eq17543
  have eq20804 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20766
  have eq20805 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20804
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20804
    | exact resolve eq20804 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20804
  have eq20806 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq20805
  have eq20825 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20806 eq20
    | exact resolve eq20 eq20806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20806
  have eq20964 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20825
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20825
    | exact resolve eq20825 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20825
  have eq21012 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20964 eq81
    | exact resolve eq81 eq20964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq21172 : (k y x) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq140 eq21012
    | exact resolve eq21012 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq21012
  have eq23512 : (k y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21172 eq14501
    | exact resolve eq14501 eq21172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21172
  have eq23522 : (k y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23512
  have eq39823 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14501 y
       have i₂ := eq23522
       grind)
    | exact superpose eq23522 eq14501
    | exact resolve eq14501 eq23522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14501 eq23522
  have eq39834 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq39823
  have eq41582 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39834 eq14525
    | exact resolve eq14525 eq39834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14525 eq39834
  have eq41633 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41582
  have eq43103 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17650
       have i₂ := eq41633
       grind)
    | exact superpose eq41633 eq17650
    | exact resolve eq17650 eq41633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17650 eq41633
  have eq43179 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43103
  have eq43183 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43179
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43179
    | exact resolve eq43179 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43179
  have eq43487 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43183 eq8941
    | (have r₁ := eq8941
       have r₂ := eq43183
       grind)
    | exact resolve eq8941 eq43183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8941 eq43183
  have eq43512 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq43487
  have eq43513 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq43512
  have eq43898 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43513 eq51
    | exact resolve eq51 eq43513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq43899 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43513 eq54
    | exact resolve eq54 eq43513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq43513
  have eq44014 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq873 eq43899
    | exact resolve eq43899 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43899
  have eq45809 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44014 eq43898
    | exact resolve eq43898 eq44014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43898 eq44014
  have eq45868 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq45809
  have eq45871 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq45868
    | exact resolve eq45868 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45868
  have eq45872 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45871 eq27
    | exact resolve eq27 eq45871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45871
  have eq45942 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq45872
       have r₂ := eq20964
       grind)
    | exact resolve eq45872 eq20964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45872
  have eq45949 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45942 eq215
    | exact resolve eq215 eq45942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq45976 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45942 eq873
    | exact resolve eq873 eq45942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq45942
  have eq46877 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45976 eq45949
    | exact resolve eq45949 eq45976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45949 eq45976
  have eq46944 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq46877
  have eq46947 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq46944
    | exact resolve eq46944 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46944
  have eq47067 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46947 eq27
    | exact resolve eq27 eq46947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46947
  have eq47143 : x = (M.op x y) := by
    first
    | (have r₁ := eq47067
       have r₂ := eq20964
       grind)
    | exact resolve eq47067 eq20964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20964 eq47067
  have eq47146 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq47143 eq20
    | exact resolve eq20 eq47143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq47237 : x = (M.op x x) := by
    first
    | exact superpose eq47143 eq871
    | exact resolve eq871 eq47143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq47318 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq47146
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47146
    | exact resolve eq47146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47146
  have eq47365 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq47318 eq26
    | exact resolve eq26 eq47318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq47670 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq47237
       grind)
    | exact superpose eq47237 eq50
    | exact resolve eq50 eq47237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq47699 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq47237
       grind)
    | exact superpose eq47237 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq47237
       grind)
    | exact resolve eq13 eq47237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47749 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq47699 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47699
  have eq47794 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq47143 eq47670
    | exact resolve eq47670 eq47143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47670
  have eq47821 : y = (M.op x y) := by
    first
    | (have i₁ := eq47794
       have i₂ := eq47237
       grind)
    | exact superpose eq47237 eq47794
    | exact resolve eq47794 eq47237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47794
  have eq47838 : y = (M.op x y) := by
    first
    | (have i₁ := eq47821
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47821
    | exact resolve eq47821 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq47821
  have eq47845 : x = y := by
    first
    | exact superpose eq47143 eq47838
    | exact resolve eq47838 eq47143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47143 eq47838
  have eq47858 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq47845
       grind)
    | exact superpose eq47845 eq24
    | exact resolve eq24 eq47845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq47845
  have eq48062 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq47858
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47858
    | exact resolve eq47858 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47858
  have eq48136 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47318 eq48062
    | exact resolve eq48062 eq47318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48062
  have eq48639 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq48136 eq47365
    | exact resolve eq47365 eq48136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47365 eq48136
  have eq49451 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq705 x
       have i₂ := eq47749 x
       grind)
    | exact superpose eq47749 eq705
    | (have j0 := eq705 x
       grind)
    | exact resolve eq705 eq47749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq47749
  have eq49512 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq49451
       have i₂ := eq47237
       grind)
    | exact superpose eq47237 eq49451
    | exact resolve eq49451 eq47237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47237 eq49451
  have eq49513 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq49512
  have eq49579 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq49513
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49513
    | exact resolve eq49513 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq49513
  have eq49632 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq47318 eq49579
    | exact resolve eq49579 eq47318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47318 eq49579
  have eq49683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48639 eq49632
    | exact resolve eq49632 eq48639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48639 eq49632
  have eq49730 : False := by grind
  exact eq49730

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation3888 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X0
       have r₂ := eq13 X0 X1
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
  have eq177 : (M.op x y) = (k y x) ∨ x = y := by
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
  have eq178 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq189 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq177
       grind)
    | exact superpose eq177 eq40
    | exact resolve eq40 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq190 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq189
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189
    | exact resolve eq189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq192 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq190
    | exact resolve eq190 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq192 eq178
    | exact resolve eq178 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq192
  have eq199 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq196
       have r₂ := eq27
       grind)
    | exact resolve eq196 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq202 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq199 eq32
    | exact resolve eq32 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq199
  have eq219 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq202
    | exact resolve eq202 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq202
  have eq220 : x = y := by grind
  clear eq219
  have eq224 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq220
       grind)
    | exact superpose eq220 eq18
    | exact resolve eq18 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq225 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq220
       grind)
    | exact superpose eq220 eq24
    | exact resolve eq24 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq220
  have eq226 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq225
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq225
    | exact resolve eq225 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq229 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq226 eq26
    | exact resolve eq26 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq226
  have eq336 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq336 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq336 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq336 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq336 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq336 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq472 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq224
       have i₂ := eq337 x
       grind)
    | exact superpose eq337 eq224
    | exact resolve eq224 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq474 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq229
       have i₂ := eq337 sF2
       grind)
    | exact superpose eq337 eq229
    | exact resolve eq229 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq337
  have eq508 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq472
       grind)
    | exact superpose eq472 eq40
    | exact resolve eq40 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq472
  have eq509 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq508
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq508
    | exact resolve eq508 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq508
  have eq511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq474 eq509
    | exact resolve eq509 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq509
  have eq513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq511
    | exact resolve eq511 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq511
  have eq515 : False := by grind
  exact eq515

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation3888 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq59 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq59 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq64
    | exact resolve eq64 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq64
  have eq85 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq95
  have eq1068 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq101 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq101 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq101 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq101 X0 X1
       grind)
    | exact resolve eq13 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1082 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1068 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1092 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1082 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq1082 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq1082 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1118 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1092 X0 X1
       have j1 := eq85 X1 (σ X0)
       grind)
    | (have r₁ := eq1092 X0 X0
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq1092 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1092
  have eq1133 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1118 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1118
    | (have j0 := eq1118 X0 X1
       grind)
    | exact resolve eq1118 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1142 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1134 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1134
    | exact resolve eq1134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1134 x y
       grind)
    | exact superpose eq1134 eq16
    | exact resolve eq16 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1338 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq1142 X0 (τ X1)
       grind)
    | exact superpose eq1142 eq18
    | exact resolve eq18 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1142
  have eq1354 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1338 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1338
    | exact resolve eq1338 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq1364 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1354 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1354
    | exact resolve eq1354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1382 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1167
       have i₂ := eq1364 x y
       grind)
    | exact superpose eq1364 eq1167
    | exact resolve eq1167 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq1364
  have eq1383 : False := by grind
  exact eq1383

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pyy_pyx_Equation3888 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
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
  clear eq24
  have eq54 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X0) ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | exact resolve eq13 eq14
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
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq74
    | (have j0 := eq74 (σ X0) (σ X1)
       grind)
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq107
    | exact resolve eq107 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq108 eq74
    | (have j0 := eq74 (σ y) (σ x)
       grind)
    | exact resolve eq74 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq573
    | exact resolve eq573 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq577 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq574
       have r₂ := eq27
       grind)
    | exact resolve eq574 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq581 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq577 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq577
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq577
       grind)
    | exact resolve eq12 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq577 eq14
    | exact resolve eq14 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq581
  have eq586 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq577 eq582
    | exact resolve eq582 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq582
  have eq591 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq586
  have eq594 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq591
    | exact resolve eq591 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq611 : ∀ X0 : G, (σ x) ≠ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq594 eq64
    | (have j0 := eq64 X0 (σ x) X0
       grind)
    | exact resolve eq64 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq54 eq611
    | (have j0 := eq611 X0
       grind)
    | exact resolve eq611 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq686 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq90 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq848 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq583 eq108
    | exact resolve eq108 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq851 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq848
  have eq893 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq594 eq851
    | exact resolve eq851 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq851 eq14
    | exact resolve eq14 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq911 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq893
  have eq914 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq911
       have r₂ := eq27
       grind)
    | exact resolve eq911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq915 : x ≠ x ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq914
       grind)
    | exact superpose eq914 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq914
       grind)
    | exact resolve eq12 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : (M.op x x) = (M.op (M.op y x) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq914
       grind)
    | exact superpose eq914 eq14
    | exact resolve eq14 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq922 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq915
  have eq925 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq916
       have i₂ := eq914
       grind)
    | exact superpose eq914 eq916
    | exact resolve eq916 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq916
  have eq933 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq925
  have eq936 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq933
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq933
    | exact resolve eq933 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq1357 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq922
       grind)
    | exact superpose eq922 eq71
    | exact resolve eq71 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1409 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1357
       have i₂ := eq936
       grind)
    | exact superpose eq936 eq1357
    | exact resolve eq1357 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq1357
  have eq1423 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1409
  have eq1425 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1423
    | exact resolve eq1423 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq1476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1425 eq74
    | (have j0 := eq74 (σ y) (σ x)
       grind)
    | exact resolve eq74 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1477 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1476
    | exact resolve eq1476 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1480 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1477
       have r₂ := eq27
       grind)
    | exact resolve eq1477 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1492 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1480 eq14
    | exact resolve eq14 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1547 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1480 eq1492
    | exact resolve eq1492 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480 eq1492
  have eq1556 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1547
  have eq1559 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1556
    | exact resolve eq1556 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1815 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq594 eq900
    | exact resolve eq900 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq1824 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq1815
  have eq1828 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1824
       have r₂ := eq27
       grind)
    | exact resolve eq1824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1830 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1828 eq14
    | exact resolve eq14 eq1828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1891 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1828 eq1830
    | exact resolve eq1830 eq1828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830
  have eq1899 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1891
  have eq1904 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1899 eq54
    | exact resolve eq54 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1899
  have eq1970 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq594 eq1904
    | exact resolve eq1904 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq1904
  have eq1982 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1970
  have eq1988 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1982 eq1828
    | exact resolve eq1828 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828 eq1982
  have eq1996 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1988
  have eq2007 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1996 eq619
    | (have j0 := eq619 X0
       grind)
    | (have r₁ := eq619 X0
       have r₂ := eq1996
       grind)
    | exact resolve eq619 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq1996
  have eq2025 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2007 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2026 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2025 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq2291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2026 eq108
    | exact resolve eq108 eq2026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq2026
  have eq2301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq2291
  have eq2307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq2301
    | exact resolve eq2301 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2301
  have eq2309 : x = (M.op y x) := by
    first
    | (have r₁ := eq2307
       have r₂ := eq27
       grind)
    | exact resolve eq2307 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq2413 : x ≠ x ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2309
       grind)
    | exact superpose eq2309 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2309
       grind)
    | exact resolve eq12 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2414 : (M.op x x) = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq2309
       grind)
    | exact superpose eq2309 eq14
    | exact resolve eq14 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2419 : ∀ X0 : G, x ≠ (M.op (M.op y x) y) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq64 y x X0
       have i₂ := eq2309
       grind)
    | exact superpose eq2309 eq64
    | (have j0 := eq64 X0 x X0
       grind)
    | exact resolve eq64 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2420 : x = (M.op x x) ∨ (k y x) = (M.op x x) := by grind
  clear eq2413
  have eq2421 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2419 X0
       have i₂ := eq2309
       grind)
    | exact superpose eq2309 eq2419
    | (have j0 := eq2419 X0
       grind)
    | exact resolve eq2419 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419
  have eq2426 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2414
       have i₂ := eq2309
       grind)
    | exact superpose eq2309 eq2414
    | exact resolve eq2414 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309 eq2414
  have eq2428 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2421 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2421
    | (have j0 := eq2421 X0
       grind)
    | exact resolve eq2421 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq2433 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2426
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2426
    | exact resolve eq2426 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq2647 : x = (M.op x y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq2420
       have i₂ := eq2433
       grind)
    | exact superpose eq2433 eq2420
    | exact resolve eq2420 eq2433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420
  have eq2648 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2647
       have i₂ := eq2433
       grind)
    | exact superpose eq2433 eq2647
    | exact resolve eq2647 eq2433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647
  have eq2652 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq2648
       grind)
    | exact superpose eq2648 eq71
    | exact resolve eq71 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648
  have eq2654 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2652
    | exact resolve eq2652 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652
  have eq2661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2654 eq74
    | (have j0 := eq74 (σ y) (σ x)
       grind)
    | exact resolve eq74 eq2654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2661
    | exact resolve eq2661 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2661
  have eq2665 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2662
       have r₂ := eq27
       grind)
    | exact resolve eq2662 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2670 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2665 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2665
       grind)
    | exact resolve eq12 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2671 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2665 eq14
    | exact resolve eq14 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2677 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2670
  have eq2683 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2665 eq2671
    | exact resolve eq2671 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665 eq2671
  have eq2696 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2683
  have eq2700 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2696
    | exact resolve eq2696 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2696
  have eq2712 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2700 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq2700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700
  have eq3202 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2677 eq2654
    | exact resolve eq2654 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2677
  have eq3209 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq3202
  have eq3213 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1559 eq3209
    | exact resolve eq3209 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559 eq3209
  have eq3240 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq3213
  have eq3244 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3240
       have r₂ := eq27
       grind)
    | exact resolve eq3240 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3240
  have eq3262 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3244 eq2712
    | (have j0 := eq2712 X0
       grind)
    | (have r₁ := eq2712 X0
       have r₂ := eq3244
       grind)
    | exact resolve eq2712 eq3244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2712 eq3244
  have eq3273 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3262 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3262
  have eq3274 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3273 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq3295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3274 eq2654
    | exact resolve eq2654 eq3274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654 eq3274
  have eq3313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3295
  have eq3322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3313
    | exact resolve eq3313 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3313
  have eq3326 : x = (M.op x y) := by
    first
    | (have r₁ := eq3322
       have r₂ := eq27
       grind)
    | exact resolve eq3322 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322
  have eq3328 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3326 eq20
    | exact resolve eq20 eq3326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3351 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq3326 eq2428
    | (have j0 := eq2428 X0
       grind)
    | (have r₁ := eq2428 X0
       have r₂ := eq3326
       grind)
    | exact resolve eq2428 eq3326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428 eq3326
  have eq3356 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq3351 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351
  have eq3381 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3328
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3328
    | exact resolve eq3328 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328
  have eq3409 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3381 eq26
    | exact resolve eq26 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3491 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq3356 y
       grind)
    | exact superpose eq3356 eq71
    | exact resolve eq71 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq3494 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq686 x
       have i₂ := eq3356 x
       grind)
    | exact superpose eq3356 eq686
    | (have j0 := eq686 x
       grind)
    | exact resolve eq686 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq3356
  have eq3512 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3494
       have i₂ := eq2433
       grind)
    | exact superpose eq2433 eq3494
    | exact resolve eq3494 eq2433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433 eq3494
  have eq3515 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq3381 eq3491
    | exact resolve eq3491 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq3530 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq3512
    | exact resolve eq3512 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3512
  have eq3533 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3515
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3515
    | exact resolve eq3515 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3515
  have eq3538 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3530
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3530
    | exact resolve eq3530 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530
  have eq3541 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3533
    | exact resolve eq3533 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3533
  have eq3545 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq3538
       have r₂ := eq3381
       grind)
    | exact resolve eq3538 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq3548 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3545
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3545
    | exact resolve eq3545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3545
  have eq3550 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3381 eq3548
    | exact resolve eq3548 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381 eq3548
  have eq3555 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq3541 eq74
    | (have j0 := eq74 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq74 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq3541
  have eq3556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq3409 eq3555
    | exact resolve eq3555 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555
  have eq3559 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3556
       have r₂ := eq27
       grind)
    | exact resolve eq3556 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3556
  have eq3596 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq3559 eq14
    | exact resolve eq14 eq3559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3608 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3559 eq3596
    | exact resolve eq3596 eq3559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3559 eq3596
  have eq3614 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3550 eq3608
    | exact resolve eq3608 eq3550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3550 eq3608
  have eq3619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3409 eq3614
    | exact resolve eq3614 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409 eq3614
  have eq3622 : False := by grind
  exact eq3622

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_pyy_pxy_Equation3888 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq178 : (M.op y y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq16 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : (M.op x y) = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq41
    | exact resolve eq41 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq555 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq554
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq554
    | exact resolve eq554 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq557 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq555
    | exact resolve eq555 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq567 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq557 eq549
    | exact resolve eq549 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq567
       have r₂ := eq27
       grind)
    | exact resolve eq567 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq580 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq574 eq16
    | exact resolve eq16 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq574 eq580
    | exact resolve eq580 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq584 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq581
    | exact resolve eq581 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq588 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq584 eq16
    | exact resolve eq16 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq589 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq179 eq588
    | exact resolve eq588 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq590 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq589
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq589
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq589 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq574 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq574
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq574
       grind)
    | exact resolve eq12 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq648 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq646
  have eq649 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq648
    | (have j1 := eq28 (σ y) (σ y)
       grind)
    | exact resolve eq648 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq652 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq590 eq649
    | exact resolve eq649 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq649
  have eq653 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq557 eq652
    | exact resolve eq652 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq654 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq653
       have r₂ := eq27
       grind)
    | exact resolve eq653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq663 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq654 eq589
    | exact resolve eq589 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq664 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq654 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq654
       grind)
    | exact resolve eq13 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq666 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq664 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq667 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq663
  have eq674 : (M.op x x) = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq667
       grind)
    | exact superpose eq667 eq16
    | exact resolve eq16 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq667 eq674
    | exact resolve eq674 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq674
  have eq679 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq676
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq676
    | exact resolve eq676 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq684 : (M.op x y) = (M.op (M.op x (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq679
       grind)
    | exact superpose eq679 eq16
    | exact resolve eq16 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq685 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq178 eq684
    | exact resolve eq684 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq690 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq685
       grind)
    | exact superpose eq685 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq724 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq690
       grind)
    | exact superpose eq690 eq41
    | exact resolve eq41 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq729 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq724
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq724
    | exact resolve eq724 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq731 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq729
    | exact resolve eq729 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq769 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq666 eq26
    | (have j1 := eq666 (σ x)
       grind)
    | exact resolve eq26 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq557 eq769
    | exact resolve eq769 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq769
  have eq785 : x = (M.op y x) := by
    first
    | (have r₁ := eq779
       have r₂ := eq27
       grind)
    | exact resolve eq779 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq791 : x ≠ x ∨ y = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq785
       grind)
    | exact superpose eq785 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq785
       grind)
    | exact resolve eq12 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq785
       grind)
    | exact superpose eq785 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : (M.op x x) = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq785
       grind)
    | exact superpose eq785 eq16
    | exact resolve eq16 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : (k x y) = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq791
  have eq795 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq793
       have i₂ := eq785
       grind)
    | exact superpose eq785 eq793
    | exact resolve eq793 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq796 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq792
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq792
    | exact resolve eq792 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq798 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq795
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq795
    | exact resolve eq795 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq803 : (M.op x y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq16 x x
       have i₂ := eq798
       grind)
    | exact superpose eq798 eq16
    | exact resolve eq16 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq808 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq803 eq178
    | exact resolve eq178 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq814 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq808
       grind)
    | exact superpose eq808 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq825 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq796
       grind)
    | exact superpose eq796 eq37
    | exact resolve eq37 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq796
  have eq828 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq825
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq825
    | exact resolve eq825 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1034 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq794
       have i₂ := eq808
       grind)
    | exact superpose eq808 eq794
    | exact resolve eq794 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq1067 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1034
       grind)
    | exact superpose eq1034 eq41
    | exact resolve eq41 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1034
  have eq1068 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1067
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1067
    | exact resolve eq1067 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1070 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1068
    | exact resolve eq1068 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1070 eq549
    | exact resolve eq549 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq1080 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1073
       have r₂ := eq27
       grind)
    | exact resolve eq1073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1089 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1080 eq16
    | exact resolve eq16 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1080 eq1089
    | exact resolve eq1089 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1095 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1091
    | exact resolve eq1091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1106 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1095 eq16
    | exact resolve eq16 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1107 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq179 eq1106
    | exact resolve eq1106 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1123 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1107 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq731 eq1123
    | exact resolve eq1123 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq1123
  have eq1129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1125
       have r₂ := eq27
       grind)
    | exact resolve eq1125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1135 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1129 eq179
    | exact resolve eq179 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1138 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1135
    | exact resolve eq1135 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1140 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1107 eq1138
    | exact resolve eq1138 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq1138
  have eq1142 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1129 eq1140
    | exact resolve eq1140 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq1140
  have eq1144 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1080 eq1142
    | exact resolve eq1142 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1168 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1144 eq828
    | exact resolve eq828 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq1170 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1144 eq1070
    | exact resolve eq1070 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1171 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1144 eq1080
    | exact resolve eq1080 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq1144
  have eq1174 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1171
  have eq1175 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1170
  have eq1177 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1168
  have eq1316 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1174 eq1095
    | exact resolve eq1095 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095 eq1174
  have eq1323 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1316
  have eq1340 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1323 eq27
    | exact resolve eq27 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1365 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1177 eq1175
    | exact resolve eq1175 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175 eq1177
  have eq1377 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1365
  have eq1383 : y = (M.op x y) := by
    first
    | (have r₁ := eq1377
       have r₂ := eq1340
       grind)
    | exact resolve eq1377 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340 eq1377
  have eq1388 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1383
       grind)
    | exact superpose eq1383 eq18
    | exact resolve eq18 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1389 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1383
       grind)
    | exact superpose eq1383 eq24
    | exact resolve eq24 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1398 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq785
       have i₂ := eq1383
       grind)
    | exact superpose eq1383 eq785
    | exact resolve eq785 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq1400 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq808
       have i₂ := eq1383
       grind)
    | exact superpose eq1383 eq808
    | exact resolve eq808 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1401 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq814 X0
       have i₂ := eq1383
       grind)
    | exact superpose eq1383 eq814
    | (have r₁ := eq814 X0
       have r₂ := eq1383
       grind)
    | exact resolve eq814 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq1383
  have eq1404 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq1401 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1405 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1404 eq1400
    | exact resolve eq1400 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1408 : (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq1404 eq1388
    | exact resolve eq1388 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1411 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1389 eq20
    | exact resolve eq20 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1504 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1405 eq38
    | exact resolve eq38 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1405
  have eq1512 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1504
    | exact resolve eq1504 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1514 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1411 eq1512
    | exact resolve eq1512 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411 eq1512
  have eq1627 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1514 eq551
    | (have j0 := eq551 (σ y)
       grind)
    | (have r₁ := eq551 (σ y)
       have r₂ := eq1514
       grind)
    | exact resolve eq551 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq1514
  have eq1628 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1627
  have eq1834 : (M.op y y) = (M.op (k x (M.op x y)) x) := by
    first
    | exact superpose eq1404 eq178
    | exact resolve eq178 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1404
  have eq1843 : (M.op y y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1408 eq1834
    | exact resolve eq1834 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq1834
  have eq1858 : x = (M.op y y) := by
    first
    | exact superpose eq1398 eq1843
    | exact resolve eq1843 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398 eq1843
  have eq1869 : x = (M.op x y) := by
    first
    | (have i₁ := eq1858
       have i₂ := eq808
       grind)
    | exact superpose eq808 eq1858
    | exact resolve eq1858 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq1858
  have eq1878 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1869
       grind)
    | exact superpose eq1869 eq22
    | exact resolve eq22 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1869
  have eq1917 : (σ x) = (σ y) := by
    first
    | exact superpose eq1878 eq1389
    | exact resolve eq1389 eq1878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq1918 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1878 eq20
    | exact resolve eq20 eq1878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1878
  have eq1952 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1917 eq26
    | exact resolve eq26 eq1917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1984 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1917 eq1628
    | exact resolve eq1628 eq1917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628 eq1917
  have eq1995 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1984 eq1952
    | exact resolve eq1952 eq1984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952 eq1984
  have eq2059 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1995 eq27
    | exact resolve eq27 eq1995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1995
  have eq2065 : False := by grind
  exact eq2065

/-- `Equation3930`: `x ◇ y = (x ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_y_pyx_Equation3930 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3930 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3930.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X3))) = (M.op (M.op X2 (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X0 (M.op X1 X3)) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X3))) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x x) ∨ x = (k y x) := by
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
  have eq75 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq104
    | exact resolve eq104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq121 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq38
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq224 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) (M.op x y))) = (k (k X0 (σ X1)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq42
    | exact resolve eq42 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq42
  have eq313 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq340 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 (τ X0)
       have i₂ := eq76 (τ X0)
       grind)
    | exact superpose eq76 eq39
    | (have j1 := eq76 (τ X0)
       grind)
    | exact resolve eq39 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq76
  have eq353 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq340 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq340
    | (have j0 := eq340 X0
       grind)
    | exact resolve eq340 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq421 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op x x)
       have i₂ := eq55 X1 x X0 x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op x x)
       have i₂ := eq55 X1 x X0 x
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X0) ≠ (M.op (M.op X0 (M.op X1 X2)) X3) ∨ (M.op (M.op X0 (M.op X1 X2)) X0) = X3 ∨ (M.op X0 (M.op X1 X2)) = (k X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 (M.op X0 (M.op X1 X3))
       have i₂ := eq55 X0 X1 (M.op X0 (M.op X1 X3)) X3
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 X3 (M.op X0 (M.op X1 X2))
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op X1 X3))
       have r₂ := eq55 X0 X1 (M.op X0 (M.op X1 X3)) X3
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X1 X3)) X0
       have r₂ := eq55 X0 X1 X0 X3
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 (M.op X2 X3)) ∨ (k (M.op X1 (M.op X2 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 X3)) X0
       have i₂ := eq55 X1 X2 X0 X3
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 (M.op X1 (M.op X2 X3)) X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op X1 X3))
       have r₂ := eq55 X0 X1 (M.op X0 (M.op X1 X3)) X3
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X1 X3)) X0
       have r₂ := eq55 X0 X1 X0 X3
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq437 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 (M.op X1 X2)) X3) ∨ (M.op (M.op X0 (M.op X1 X2)) X0) = X3 ∨ (M.op X0 (M.op X1 X2)) = (k X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq429 X0 X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq429
    | (have j0 := eq429 X0 X1 X2 X3
       grind)
    | exact resolve eq429 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq441 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = X3 ∨ (M.op X0 X1) ≠ (M.op (M.op X0 (M.op X1 X2)) X3) ∨ (M.op X0 (M.op X1 X2)) = (k X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq437 X0 X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq437
    | (have j0 := eq437 X0 X1 X2 X3
       grind)
    | (have r₁ := eq437 X0 X1 X2 X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq437 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq449 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq421 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq421
    | (have j0 := eq421 x y X0
       grind)
    | exact resolve eq421 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq421
    | (have j0 := eq421 (σ x) (σ y) X0
       grind)
    | exact resolve eq421 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq428 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq428
    | (have j0 := eq428 x y
       grind)
    | exact resolve eq428 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq92 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq92 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq12 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X1)) (σ X0)) = (M.op (σ X0) (M.op (σ X0) (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    grind
  clear eq92
  have eq754 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq741 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq755 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq754 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq757 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (k (M.op (σ X0) (σ X1)) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq744 X0 X1
       have i₂ := eq421 (σ X0) (σ X1) (σ X0)
       grind)
    | exact superpose eq421 eq744
    | (have j0 := eq744 X0 X1
       grind)
    | exact resolve eq744 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq758 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq755 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq755
    | (have j0 := eq755 X0 X1
       grind)
    | exact resolve eq755 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq790 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq224 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq224
    | (have j0 := eq224 X0 x
       grind)
    | exact resolve eq224 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq1689 : ∀ X0 X1 : G, (k (k X1 (σ X0)) (σ (M.op x y))) = (σ (k (M.op X0 (τ X1)) (M.op x y))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq230 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq230
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq3778 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq313 X0
       have i₂ := eq421 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq421 eq313
    | exact resolve eq313 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq3891 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3778 X0
       have i₂ := eq353 X0
       grind)
    | exact superpose eq353 eq3778
    | (have j1 := eq353 X0
       grind)
    | exact resolve eq3778 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq3892 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op X0 X0) = (M.op X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3778 X0
       have i₂ := eq11 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact superpose eq11 eq3778
    | (have j1 := eq11 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact resolve eq3778 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3937 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3891 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3891
    | (have j0 := eq3891 X0
       grind)
    | exact resolve eq3891 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891
  have eq3938 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3937 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937
  have eq4525 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (k X0 x)) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq159 eq428
    | (have j1 := eq159 X0
       grind)
    | exact resolve eq428 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq4528 : ∀ X0 : G, (σ (k X0 x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq159 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq5805 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op X1 (M.op X2 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq431 X0 X1 X2 X3
       have i₂ := eq421 X2 X3 X1
       grind)
    | exact superpose eq421 eq431
    | (have j0 := eq431 X0 X1 X2 X3
       grind)
    | (have r₁ := eq431 X0 (M.op X0 X1) X2 X3
       have r₂ := eq421 X0 X1 X0
       grind)
    | (have r₁ := eq431 (M.op X0 X1) X0 X2 X3
       have r₂ := eq421 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq431 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq5806 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X2) = (M.op X0 X0) ∨ (k (M.op X1 X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5805 X0 X1 X2 x
       have i₂ := eq421 X2 x X1
       grind)
    | exact superpose eq421 eq5805
    | (have j0 := eq5805 X0 X1 X2 x
       grind)
    | (have r₁ := eq5805 X0 (M.op X0 X1) X2 x
       have r₂ := eq421 X0 X1 X0
       grind)
    | (have r₁ := eq5805 (M.op X0 X1) X0 X2 x
       have r₂ := eq421 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq5805 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5805
  have eq5835 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5806 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5806
  have eq5948 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq758 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq758
    | (have j0 := eq758 x X0
       grind)
    | exact resolve eq758 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq7807 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X3) ∨ (M.op X0 X1) = X3 ∨ (M.op X0 (M.op X1 X2)) = (k X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq441 X0 X1 X2 X3
       have i₂ := eq421 X1 X2 X0
       grind)
    | exact superpose eq421 eq441
    | (have j0 := eq441 X0 X1 X2 X3
       grind)
    | exact resolve eq441 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq7808 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X3) ∨ (M.op X0 X1) = (k X3 (M.op X0 X1)) ∨ (M.op X0 X1) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7807 x X0 X1 X3
       have i₂ := eq421 X0 X1 x
       grind)
    | exact superpose eq421 eq7807
    | (have j0 := eq7807 X0 X1 x X3
       grind)
    | exact resolve eq7807 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7807
  have eq7833 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) X0) ∨ (M.op x y) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq7808 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7808
    | (have j0 := eq7808 x y X0
       grind)
    | exact resolve eq7808 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7808
  have eq7965 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (k (M.op (σ X0) (σ y)) (σ X0)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq757 X0 X0
       have i₂ := eq94 X0
       grind)
    | (have i₁ := eq757 X0 y
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq757
    | (have j0 := eq757 X0 y
       have j1 := eq94 X0
       grind)
    | exact resolve eq757 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq757
  have eq8084 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (k (M.op (σ X0) (σ y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7965 X0
       have i₂ := eq3938 X0
       grind)
    | exact superpose eq3938 eq7965
    | (have j0 := eq7965 X0
       grind)
    | exact resolve eq7965 eq3938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3938 eq7965
  have eq8085 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (k (M.op (σ X0) (σ y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq8084 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8084
  have eq17162 : (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq5835 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq5835
    | (have j0 := eq5835 x y
       grind)
    | exact resolve eq5835 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17165 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq5835
    | (have j0 := eq5835 (σ x) (σ y)
       grind)
    | exact resolve eq5835 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17231 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (k (M.op x y) x) := by grind
  have eq17244 : (M.op x x) = (k (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq449 eq17231
    | exact resolve eq17231 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17231
  have eq17259 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq17165
  have eq17272 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq450 eq17259
    | exact resolve eq17259 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq17259
  have eq17284 : x ≠ (M.op x x) ∨ x = (k (M.op x y) x) := by grind
  clear eq17244
  have eq17290 : x ≠ (M.op x y) ∨ x = (k (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq17284
       have i₂ := eq17162
       grind)
    | exact superpose eq17162 eq17284
    | exact resolve eq17284 eq17162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17284
  have eq17291 : x ≠ (M.op x y) ∨ x = (k (M.op x y) x) := by grind
  clear eq17290
  have eq17303 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq17603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17603
    | exact resolve eq17603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17603
  have eq17615 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17604
       have r₂ := eq28
       grind)
    | exact resolve eq17604 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17604
  have eq17619 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17615
    | exact resolve eq17615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17615
  have eq17624 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17619 eq75
    | (have r₁ := eq75
       have r₂ := eq17619
       grind)
    | exact resolve eq75 eq17619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq17638 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq17619
  have eq17641 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq17624
  have eq17652 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17641
       have r₂ := eq17638
       grind)
    | exact resolve eq17641 eq17638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17638 eq17641
  have eq17661 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq17652
  have eq17676 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17661
    | exact resolve eq17661 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17661
  have eq17685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq106 eq17676
    | exact resolve eq17676 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17676 eq106
    | exact resolve eq106 eq17676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq17676
  have eq17699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq17690
  have eq17700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq17685
  have eq17701 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq17699
       have r₂ := eq28
       grind)
    | exact resolve eq17699 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17699
  have eq17702 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17700
       have r₂ := eq28
       grind)
    | exact resolve eq17700 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17700
  have eq17709 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  have eq17720 : y ≠ (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  have eq17724 : (M.op x x) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq449 eq17709
    | exact resolve eq17709 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17709
  have eq17734 : (τ (σ x)) = (k y x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq17701 eq81
    | exact resolve eq81 eq17701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17701
  have eq17753 : x = (k y x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq29 eq17734
    | exact resolve eq17734 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17734
  have eq17760 : y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq17753
       have r₂ := eq74
       grind)
    | exact resolve eq17753 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq17753
  have eq17770 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq17760
  have eq17784 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq17770
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17770
    | exact resolve eq17770 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17770
  have eq17795 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq17784
       grind)
    | exact superpose eq17784 eq71
    | exact resolve eq71 eq17784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17784
  have eq17814 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq21 eq17795
    | exact resolve eq17795 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17795
  have eq87648 : (σ (M.op x x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17724 eq121
    | exact resolve eq121 eq17724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17724
  have eq93045 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87648
       have i₂ := eq17702
       grind)
    | exact superpose eq17702 eq87648
    | exact resolve eq87648 eq17702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17702 eq87648
  have eq93162 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq93045
  have eq93172 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq93162
       have r₂ := eq17720
       grind)
    | exact resolve eq93162 eq17720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17720 eq93162
  have eq93176 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq93172
    | exact resolve eq93172 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93172
  have eq124040 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq5948 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5948
    | (have j0 := eq5948 y
       grind)
    | exact resolve eq5948 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5948
  have eq124061 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq124040
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq124040
    | exact resolve eq124040 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124040
  have eq124116 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | exact superpose eq27 eq124061
    | exact resolve eq124061 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124061
  have eq124168 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq124116
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq124116
    | exact resolve eq124116 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124116
  have eq238681 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1689 sF0 x
       have i₂ := eq5835 sF0 (τ x)
       grind)
    | exact superpose eq5835 eq1689
    | (have j0 := eq1689 (M.op x y) X0
       have j1 := eq5835 (M.op x y) (τ X0)
       grind)
    | exact resolve eq1689 eq5835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq238843 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq238681 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238681
  have eq238857 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq238843
    | (have j0 := eq238843 X0
       grind)
    | exact resolve eq238843 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238843
  have eq238903 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (τ X0)) ∨ (σ (M.op x y)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq449 eq238857
    | (have j0 := eq238857 X0
       grind)
    | exact resolve eq238857 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238857
  have eq238943 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (σ (M.op x y)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq523 eq238903
    | (have j0 := eq238903 X0
       grind)
    | exact resolve eq238903 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238903
  have eq238953 : ∀ X0 : G, (τ X0) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (σ (M.op x y)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq449 eq238943
    | (have j0 := eq238943 X0
       grind)
    | exact resolve eq238943 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq238943
  have eq238963 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq523 eq238953
    | (have j0 := eq238953 X0
       grind)
    | exact resolve eq238953 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq238953
  have eq352744 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8085 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8085
    | (have j0 := eq8085 x
       grind)
    | exact resolve eq8085 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8085
  have eq352833 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq352744
    | exact resolve eq352744 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352744
  have eq352883 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq352833
    | exact resolve eq352833 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352833
  have eq352903 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq352883
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq352883
    | exact resolve eq352883 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352883
  have eq352919 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq352903
    | exact resolve eq352903 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352903
  have eq363720 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (M.op X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5835 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq3892 X0
       grind)
    | exact superpose eq3892 eq5835
    | (have j0 := eq5835 X0 (σ (M.op (τ X0) (τ X0)))
       have j1 := eq3892 X0
       grind)
    | exact resolve eq5835 eq3892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3892 eq5835
  have eq363907 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (M.op X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have j0 := eq363720 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363720
  have eq364029 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq363907 X0
       have j1 := eq12 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | (have r₁ := eq363907 x
       have r₂ := eq12 (σ (M.op (τ x) (τ x))) x
       grind)
    | exact resolve eq363907 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363907
  have eq364148 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq364029 X0
       have i₂ := eq3778 X0
       grind)
    | exact superpose eq3778 eq364029
    | (have j0 := eq364029 X0
       grind)
    | exact resolve eq364029 eq3778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778 eq364029
  have eq1494635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq124168 eq17814
    | exact resolve eq17814 eq124168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124168
  have eq1494992 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq1494635
       have r₂ := eq28
       grind)
    | exact resolve eq1494635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494635
  have eq1834796 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by grind
  clear eq1494992
  have eq1834818 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq27 eq1834796
    | exact resolve eq1834796 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834796
  have eq1834873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq1834818 eq17814
    | exact resolve eq17814 eq1834818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17814 eq1834818
  have eq1835501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1834873
  have eq1835518 : (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq1835501
       have r₂ := eq28
       grind)
    | exact resolve eq1835501 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835501
  have eq1835572 : (τ (σ x)) = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq1835518 eq81
    | exact resolve eq81 eq1835518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835518
  have eq1836100 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq1835572
    | exact resolve eq1835572 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835572
  have eq1836101 : x = (k y x) := by grind
  clear eq1836100
  have eq1836119 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1836101
       grind)
    | exact superpose eq1836101 eq71
    | exact resolve eq71 eq1836101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1836297 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4525 y
       have i₂ := eq1836101
       grind)
    | exact superpose eq1836101 eq4525
    | (have j0 := eq4525 y
       grind)
    | exact resolve eq4525 eq1836101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4525
  have eq1836300 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4528 y
       have i₂ := eq1836101
       grind)
    | exact superpose eq1836101 eq4528
    | (have j0 := eq4528 y
       grind)
    | exact resolve eq4528 eq1836101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4528
  have eq1836314 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1836300
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1836300
    | exact resolve eq1836300 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836300
  have eq1836317 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1836297
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1836297
    | exact resolve eq1836297 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836297
  have eq1836389 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1836119
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1836119
    | exact resolve eq1836119 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836119
  have eq1836397 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1836314
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1836314
    | exact resolve eq1836314 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836314
  have eq1836398 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1836317
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1836317
    | exact resolve eq1836317 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836317
  have eq1836421 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq1836397
    | exact resolve eq1836397 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836397
  have eq1836422 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq1836398
    | exact resolve eq1836398 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836398
  have eq1836432 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1836421
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1836421
    | exact resolve eq1836421 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836421
  have eq1836433 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1836422
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1836422
    | exact resolve eq1836422 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1836422
  have eq1842899 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq1836433
       have r₂ := eq1836432
       grind)
    | exact resolve eq1836433 eq1836432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836432 eq1836433
  have eq2543540 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1836389 eq352919
    | exact resolve eq352919 eq1836389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352919
  have eq2543541 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2543540
  have eq2544071 : (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) = (σ (M.op (k y x) (k y x))) ∨ (k (σ y) (σ x)) = (σ (M.op (k y x) (k y x))) := by
    first
    | exact superpose eq81 eq364148
    | exact resolve eq364148 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364148
  have eq2545571 : (σ (M.op x x)) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (k (σ y) (σ x)) = (σ (M.op (k y x) (k y x))) := by
    first
    | (have i₁ := eq2544071
       have i₂ := eq1836101
       grind)
    | exact superpose eq1836101 eq2544071
    | exact resolve eq2544071 eq1836101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544071
  have eq2546143 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (k (σ y) (σ x)) = (σ (M.op (k y x) (k y x))) := by
    first
    | exact superpose eq1836389 eq2545571
    | exact resolve eq2545571 eq1836389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545571
  have eq2546437 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2546143
       have i₂ := eq1836101
       grind)
    | exact superpose eq1836101 eq2546143
    | exact resolve eq2546143 eq1836101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546143
  have eq2546596 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | exact superpose eq1836389 eq2546437
    | exact resolve eq2546437 eq1836389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546437
  have eq2546729 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq2546596
       have i₂ := eq17162
       grind)
    | exact superpose eq17162 eq2546596
    | exact resolve eq2546596 eq17162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17162 eq2546596
  have eq2548205 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq21 eq2546729
    | exact resolve eq2546729 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546729
  have eq2548657 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq21 eq2548205
    | exact resolve eq2548205 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548205
  have eq2549100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq2548657 eq1842899
    | exact resolve eq1842899 eq2548657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842899 eq2548657
  have eq2549155 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2549100
       have r₂ := eq28
       grind)
    | exact resolve eq2549100 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549100
  have eq2550101 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2549155 eq121
    | exact resolve eq121 eq2549155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549155
  have eq2550441 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2550101
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2550101
    | exact resolve eq2550101 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550101
  have eq2550579 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2550441 eq93176
    | exact resolve eq93176 eq2550441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550441
  have eq2550805 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2550579
  have eq2551192 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2550805
  have eq2551224 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2551192
       have i₂ := eq1836101
       grind)
    | exact superpose eq1836101 eq2551192
    | exact resolve eq2551192 eq1836101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551192
  have eq2551226 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2551224
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2551224
    | exact resolve eq2551224 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551224
  have eq2551237 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2551226 eq81
    | exact resolve eq81 eq2551226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2551226
  have eq2552846 : (k y x) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq132 eq2551237
    | exact resolve eq2551237 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq2551237
  have eq2553001 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2552846
       have i₂ := eq1836101
       grind)
    | exact superpose eq1836101 eq2552846
    | exact resolve eq2552846 eq1836101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552846
  have eq2553077 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq2553001
       have r₂ := eq17291
       grind)
    | exact resolve eq2553001 eq17291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17291 eq2553001
  have eq2553109 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2553077 eq121
    | exact resolve eq121 eq2553077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq2553077
  have eq2553449 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2553109
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2553109
    | exact resolve eq2553109 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553109
  have eq2553587 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2553449 eq93176
    | exact resolve eq93176 eq2553449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93176 eq2553449
  have eq2553813 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2553587
  have eq2554202 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2553813
  have eq2554234 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2554202
       have i₂ := eq1836101
       grind)
    | exact superpose eq1836101 eq2554202
    | exact resolve eq2554202 eq1836101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836101 eq2554202
  have eq2554236 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2554234
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2554234
    | exact resolve eq2554234 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2554234
  have eq2554239 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2554236 eq29
    | exact resolve eq29 eq2554236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2554236
  have eq2556178 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2554239
    | exact resolve eq2554239 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2554239
  have eq2556179 : x = (M.op x y) := by grind
  clear eq2556178
  have eq2556587 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2556179 eq21
    | exact resolve eq21 eq2556179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2556592 : (σ (k y x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2556179 eq73
    | exact resolve eq73 eq2556179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq2556992 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | exact superpose eq2556179 eq7833
    | exact resolve eq7833 eq2556179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7833
  have eq2558458 : (k (σ y) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2556592
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq2556592
    | exact resolve eq2556592 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq2556592
  have eq2558462 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2556587
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2556587
    | exact resolve eq2556587 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556587
  have eq2558709 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1836389 eq2558458
    | exact resolve eq2558458 eq1836389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836389 eq2558458
  have eq2559019 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2558462 eq27
    | exact resolve eq27 eq2558462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2559347 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2558462 eq17272
    | exact resolve eq17272 eq2558462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17272
  have eq2559348 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2558462 eq17303
    | exact resolve eq17303 eq2558462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17303
  have eq2560477 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2558462 eq2543541
    | exact resolve eq2543541 eq2558462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543541
  have eq2560479 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2560477
       have r₂ := eq28
       grind)
    | exact resolve eq2560477 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560477
  have eq2562176 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2558462 eq2558709
    | exact resolve eq2558709 eq2558462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558709
  have eq2583522 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2559347 eq238963
    | (have j0 := eq238963 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq238963 eq2559347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238963 eq2559347
  have eq2583548 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
  clear eq2583522
  have eq2583554 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2583548
       have i₂ := eq421 sF1 sF1 sF1
       grind)
    | exact superpose eq421 eq2583548
    | exact resolve eq2583548 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq2583548
  have eq2583555 : (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2583554
       have r₂ := eq2559348
       grind)
    | exact resolve eq2583554 eq2559348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559348 eq2583554
  have eq2583556 : x = (M.op x (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2556179 eq2583555
    | exact resolve eq2583555 eq2556179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583555
  have eq2583557 : x = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2556179 eq2583556
    | exact resolve eq2583556 eq2556179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556179 eq2583556
  have eq2673538 : x ≠ x ∨ x = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2583557 eq2556992
    | (have j0 := eq2556992 (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq2556992 (τ (M.op (σ x) (σ y)))
       have r₂ := eq2583557
       grind)
    | exact resolve eq2556992 eq2583557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556992 eq2583557
  have eq2673586 : x ≠ x ∨ x = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
  clear eq2673538
  have eq2673587 : x = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
  clear eq2673586
  have eq2673592 : x = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2673587
       have i₂ := eq790 sF4
       grind)
    | exact superpose eq790 eq2673587
    | exact resolve eq2673587 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq2673587
  have eq2673598 : x = (τ (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2558462 eq2673592
    | exact resolve eq2673592 eq2558462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673592
  have eq2674857 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2560479 eq2673598
    | exact resolve eq2673598 eq2560479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560479 eq2673598
  have eq2675371 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2674857
  have eq2675706 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq2675371
       have r₂ := eq28
       grind)
    | exact resolve eq2675371 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2675371
  have eq2676111 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2675706
  have eq2676140 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2559019 eq2676111
    | exact resolve eq2676111 eq2559019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559019 eq2676111
  have eq2676142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2562176 eq2676140
    | exact resolve eq2676140 eq2562176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562176 eq2676140
  have eq2676143 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq2676142
       have r₂ := eq28
       grind)
    | exact resolve eq2676142 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676142
  have eq2676144 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2676143 eq15
    | exact resolve eq15 eq2676143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676143
  have eq2676988 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2676144
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2676144
    | exact resolve eq2676144 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2676144
  have eq2677133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2558462 eq2676988
    | exact resolve eq2676988 eq2558462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558462 eq2676988
  have eq2677221 : False := by grind
  exact eq2677221
