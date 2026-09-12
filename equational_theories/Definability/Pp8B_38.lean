import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_y_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 X0
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq550 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq552 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq174 eq550
    | exact resolve eq550 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq844 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq865 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq874 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq866 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq866
    | (have j0 := eq866 (σ X0)
       grind)
    | exact resolve eq866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq1776 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1802 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1806 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1802 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1802
    | exact resolve eq1802 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq1811 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1776 X0 x x X3 X4
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1776
    | exact resolve eq1776 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776
  have eq1857 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1806 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1806
    | (have j0 := eq1806 x y
       grind)
    | exact resolve eq1806 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5701 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq844
       grind)
    | exact superpose eq844 eq39
    | exact resolve eq39 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq844
  have eq5702 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5701
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5701
    | exact resolve eq5701 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5701
  have eq5705 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq5702
    | exact resolve eq5702 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5702
  have eq15015 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0 x X0
       have i₂ := eq1811 X0 X0 x
       grind)
    | exact superpose eq1811 eq176
    | exact resolve eq176 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq15049 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15015 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq15015
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq15015 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15054 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1811 X0 X0 X0
       have i₂ := eq15015 X0
       grind)
    | exact superpose eq15015 eq1811
    | exact resolve eq1811 eq15015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15066 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1811 (M.op X0 X0) X0 x
       have i₂ := eq15015 X0
       grind)
    | exact superpose eq15015 eq1811
    | exact resolve eq1811 eq15015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15069 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15049 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15049
  have eq15290 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq15054 X0
       grind)
    | exact superpose eq15054 eq178
    | exact resolve eq178 eq15054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15300 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0)
       have i₂ := eq15054 X0
       grind)
    | exact superpose eq15054 eq178
    | exact resolve eq178 eq15054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15318 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15300 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq15300
    | exact resolve eq15300 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15300
  have eq15325 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15318 X0
       have i₂ := eq15290 X0
       grind)
    | exact superpose eq15290 eq15318
    | exact resolve eq15318 eq15290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15318
  have eq15360 : (σ (M.op y y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq15290 y
       grind)
    | exact superpose eq15290 eq40
    | exact resolve eq40 eq15290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15290
  have eq16154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5705 eq854
    | exact resolve eq854 eq5705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16163 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16154
       have r₂ := eq27
       grind)
    | exact resolve eq16154 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16154
  have eq16174 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16163 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16163
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16163
       grind)
    | exact resolve eq12 eq16163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16163
  have eq16186 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq16174
  have eq16187 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq16186
  have eq16197 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5705 eq16187
    | exact resolve eq16187 eq5705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16187
  have eq16217 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16197 eq178
    | exact resolve eq178 eq16197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq16221 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16197 eq15054
    | exact resolve eq15054 eq16197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16235 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16197 eq1806
    | exact resolve eq1806 eq16197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16197
  have eq16240 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq16235
    | exact resolve eq16235 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16235
  have eq16244 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5705 eq16217
    | exact resolve eq16217 eq5705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5705 eq16217
  have eq16248 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16221 eq16244
    | exact resolve eq16244 eq16221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16221 eq16244
  have eq16268 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1806 y x
       have i₂ := eq16240
       grind)
    | exact superpose eq16240 eq1806
    | exact resolve eq1806 eq16240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16269 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1811 y x x
       have i₂ := eq16240
       grind)
    | exact superpose eq16240 eq1811
    | exact resolve eq1811 eq16240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16274 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16269 X0
       have i₂ := eq552 X0
       grind)
    | (have i₁ := eq16269 X0
       have i₂ := eq552 (M.op y X0)
       grind)
    | exact superpose eq552 eq16269
    | exact resolve eq16269 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16269
  have eq16306 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1806 y x
       have i₂ := eq16248
       grind)
    | exact superpose eq16248 eq1806
    | exact resolve eq1806 eq16248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16307 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1811 y x x
       have i₂ := eq16248
       grind)
    | exact superpose eq16248 eq1811
    | exact resolve eq1811 eq16248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16248
  have eq16312 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16307 X0
       have i₂ := eq552 X0
       grind)
    | (have i₁ := eq16307 X0
       have i₂ := eq552 (M.op y X0)
       grind)
    | exact superpose eq552 eq16307
    | exact resolve eq16307 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq16307
  have eq18329 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq16274 X0
       grind)
    | exact superpose eq16274 eq16
    | exact resolve eq16 eq16274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18368 : ∀ X0 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq16268 eq18329
    | exact resolve eq18329 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16268 eq18329
  have eq18392 : ∀ X0 : G, x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15015 x
       have i₂ := eq18368 X0
       grind)
    | exact superpose eq18368 eq15015
    | (have j1 := eq18368 x
       grind)
    | exact resolve eq15015 eq18368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15015
  have eq18409 : ∀ X0 : G, y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1806 x x
       have i₂ := eq18368 X0
       grind)
    | exact superpose eq18368 eq1806
    | (have j1 := eq18368 X0
       grind)
    | exact resolve eq1806 eq18368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18368
  have eq18414 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18409 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18409
    | (have j0 := eq18409 X0
       grind)
    | exact resolve eq18409 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18409
  have eq18455 : y = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15325 y
       have i₂ := eq18414 y
       grind)
    | exact superpose eq18414 eq15325
    | exact resolve eq15325 eq18414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18660 : x ≠ x ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have j0 := eq18392 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18392
  have eq18661 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18660
  have eq18700 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16240
       have i₂ := eq18661
       grind)
    | exact superpose eq18661 eq16240
    | exact resolve eq16240 eq18661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16240
  have eq18701 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16274 x
       have i₂ := eq18661
       grind)
    | exact superpose eq18661 eq16274
    | exact resolve eq16274 eq18661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16274
  have eq18717 : y = (M.op (M.op (M.op y y) x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15066 y x
       have i₂ := eq18661
       grind)
    | exact superpose eq18661 eq15066
    | exact resolve eq15066 eq18661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15066 eq18661
  have eq18718 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq18701
  have eq18719 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq18700
  have eq18726 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18718
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18718
    | exact resolve eq18718 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18718
  have eq18826 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq15054 x
       have i₂ := eq18719
       grind)
    | exact superpose eq18719 eq15054
    | exact resolve eq15054 eq18719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15054
  have eq18829 : y = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq15325 x
       have i₂ := eq18719
       grind)
    | exact superpose eq18719 eq15325
    | exact resolve eq15325 eq18719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15325 eq18719
  have eq18854 : y = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18455 eq18829
    | exact resolve eq18829 eq18455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18455 eq18829
  have eq18855 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18414 eq18826
    | (have j1 := eq18414 y
       grind)
    | exact resolve eq18826 eq18414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18414 eq18826
  have eq18918 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1806 x x
       have i₂ := eq18726
       grind)
    | exact superpose eq18726 eq1806
    | exact resolve eq1806 eq18726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18726
  have eq18924 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18918
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18918
    | exact resolve eq18918 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18918
  have eq18925 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18924
  have eq18941 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18925 eq27
    | exact resolve eq27 eq18925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19110 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq874 y
       have i₂ := eq18854
       grind)
    | exact superpose eq18854 eq874
    | (have j0 := eq874 y
       grind)
    | exact resolve eq874 eq18854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq18854
  have eq19116 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19110
  have eq19118 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19116
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19116
    | exact resolve eq19116 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19116
  have eq20390 : y = (M.op (M.op (k y y) x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18717
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq18717
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq18717 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18717
  have eq20420 : y = (M.op (M.op (k y y) x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by grind
  clear eq20390
  have eq20455 : y = (M.op (M.op (k y y) (M.op x y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq18855 eq20420
    | exact resolve eq20420 eq18855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18855 eq20420
  have eq20482 : (M.op x y) = (M.op (M.op (k (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq18925 eq20455
    | exact resolve eq20455 eq18925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20455
  have eq20501 : (M.op x y) = (M.op (M.op (k (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18925 eq20482
    | exact resolve eq20482 eq18925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18925 eq20482
  have eq20517 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq15069 eq20501
    | (have j1 := eq15069 (M.op x y)
       grind)
    | exact resolve eq20501 eq15069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15069 eq20501
  have eq20518 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq20517
  have eq20576 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq20518 eq1811
    | exact resolve eq1811 eq20518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20580 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq181 eq20576
    | exact resolve eq20576 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq20576
  have eq20714 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq20580 eq16
    | exact resolve eq16 eq20580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20580
  have eq20754 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq20518 eq20714
    | exact resolve eq20714 eq20518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20518 eq20714
  have eq20810 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq20754 eq16
    | exact resolve eq16 eq20754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20827 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq20754 eq20810
    | exact resolve eq20810 eq20754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20754 eq20810
  have eq21387 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq20827 X0 X1
       grind)
    | exact superpose eq20827 eq16
    | exact resolve eq16 eq20827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21881 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19118 eq21387
    | exact resolve eq21387 eq19118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19118 eq21387
  have eq21953 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21881 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21881
  have eq22516 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21953 eq20827
    | exact resolve eq20827 eq21953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20827 eq21953
  have eq22530 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22516 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22516
  have eq22846 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22530 eq26
    | (have j1 := eq22530 (σ x)
       grind)
    | exact resolve eq26 eq22530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22530
  have eq22858 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22846
  have eq22872 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22858 eq27
    | exact resolve eq27 eq22858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22858
  have eq36700 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq16312 X0
       grind)
    | exact superpose eq16312 eq16
    | exact resolve eq16 eq16312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16312
  have eq36784 : ∀ X0 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq16306 eq36700
    | exact resolve eq36700 eq16306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16306 eq36700
  have eq36859 : ∀ X0 : G, y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1806 x x
       have i₂ := eq36784 X0
       grind)
    | exact superpose eq36784 eq1806
    | (have j1 := eq36784 X0
       grind)
    | exact resolve eq1806 eq36784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806 eq36784
  have eq36899 : ∀ X0 : G, y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36859 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36859
    | (have j0 := eq36859 X0
       grind)
    | exact resolve eq36859 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36859
  have eq36923 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36899 X0
       grind)
    | (have r₁ := eq36899 X0
       have r₂ := eq18941
       grind)
    | exact resolve eq36899 eq18941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18941 eq36899
  have eq37008 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op (M.op y X0) X1) (M.op y X0)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1811 y X0 X1
       have i₂ := eq36923 (M.op (M.op y X0) X1)
       grind)
    | exact superpose eq36923 eq1811
    | exact resolve eq1811 eq36923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq37051 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq36923 eq37008
    | exact resolve eq37008 eq36923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37008
  have eq37373 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq37051 y X0
       have i₂ := eq36923 X0
       grind)
    | exact superpose eq36923 eq37051
    | exact resolve eq37051 eq36923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36923 eq37051
  have eq37553 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq37373 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37373
  have eq37798 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq37553 x
       grind)
    | exact superpose eq37553 eq18
    | (have j1 := eq37553 x
       grind)
    | exact resolve eq18 eq37553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37553
  have eq37886 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq37798
  have eq38984 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37886 eq28
    | exact resolve eq28 eq37886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq37886
  have eq39077 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq38984
    | exact resolve eq38984 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38984
  have eq39089 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq39077
       grind)
    | exact superpose eq39077 eq24
    | exact resolve eq24 eq39077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39186 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq39089
    | exact resolve eq39089 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39089
  have eq39265 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39186 eq22872
    | (have r₁ := eq22872
       have r₂ := eq39186
       grind)
    | exact resolve eq22872 eq39186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22872 eq39186
  have eq39298 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq39265
  have eq39299 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq39298
  have eq39358 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39299 eq31
    | exact resolve eq31 eq39299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq39299
  have eq39595 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq39358
    | exact resolve eq39358 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq39358
  have eq39660 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39077 eq39595
    | exact resolve eq39595 eq39077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39077 eq39595
  have eq39661 : x = (M.op x y) := by grind
  clear eq39660
  have eq39678 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq39661
       grind)
    | exact superpose eq39661 eq18
    | exact resolve eq18 eq39661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq39679 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq39661
       grind)
    | exact superpose eq39661 eq22
    | exact resolve eq22 eq39661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq39705 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1857
       have i₂ := eq39661
       grind)
    | exact superpose eq39661 eq1857
    | exact resolve eq1857 eq39661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39661
  have eq39823 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq39679 eq20
    | exact resolve eq20 eq39679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40247 : y = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq39678 eq174
    | exact resolve eq174 eq39678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq40323 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1857 eq40247
    | exact resolve eq40247 eq1857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857 eq40247
  have eq40329 : y = (M.op x y) := by
    first
    | exact superpose eq39678 eq40323
    | exact resolve eq40323 eq39678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39678 eq40323
  have eq40338 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq40329
       grind)
    | exact superpose eq40329 eq24
    | exact resolve eq24 eq40329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq40362 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq15360
       have i₂ := eq40329
       grind)
    | exact superpose eq40329 eq15360
    | exact resolve eq15360 eq40329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15360 eq40329
  have eq40403 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq39705 eq40362
    | exact resolve eq40362 eq39705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39705 eq40362
  have eq40421 : (σ x) = (σ y) := by
    first
    | exact superpose eq39679 eq40338
    | exact resolve eq40338 eq39679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39679 eq40338
  have eq40422 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq40403
    | exact resolve eq40403 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq40403
  have eq40432 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq40421 eq40422
    | exact resolve eq40422 eq40421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40422
  have eq40434 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq39823 eq40432
    | exact resolve eq40432 eq39823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40432
  have eq40435 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40421 eq26
    | exact resolve eq26 eq40421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq40485 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40421 eq854
    | exact resolve eq854 eq40421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq40421
  have eq40563 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq40485
  have eq40568 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40434 eq40563
    | exact resolve eq40563 eq40434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40434 eq40563
  have eq40616 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40435 eq40568
    | exact resolve eq40568 eq40435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40435 eq40568
  have eq40617 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq40616
  have eq40689 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq40617 eq27
    | exact resolve eq27 eq40617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40617
  have eq40736 : False := by grind
  exact eq40736

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
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
  have eq78 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq78 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  clear eq73
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq133 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq23 eq38
  have eq531 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x X0 X1 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq544 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq544
    | exact resolve eq544 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq551 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq531 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq531
    | exact resolve eq531 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq3514 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x X0
       have i₂ := eq551 X0 X0 x
       grind)
    | exact superpose eq551 eq53
    | exact resolve eq53 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3555 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq540 x x
       have i₂ := eq3514 x
       grind)
    | exact superpose eq3514 eq540
    | exact resolve eq540 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq3556 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq542 sF2 sF2
       have i₂ := eq3514 sF2
       grind)
    | exact superpose eq3514 eq542
    | exact resolve eq542 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq3557 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq551 X0 X0 X0
       have i₂ := eq3514 X0
       grind)
    | exact superpose eq3514 eq551
    | exact resolve eq551 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq3580 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq3557
  have eq3642 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3580 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq80 X0 X1 X2
       grind)
    | exact superpose eq80 eq3580
    | (have j1 := eq80 X0 X1 X2
       grind)
    | exact resolve eq3580 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq3580
  have eq3661 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3642 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3642
  have eq4028 : (M.op x y) = (k (M.op x y) (M.op (M.op x x) x)) := by
    first
    | exact superpose eq3555 eq3661
    | exact resolve eq3661 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555
  have eq4030 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq3556 eq3661
    | exact resolve eq3661 eq3556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3556 eq3661
  have eq4070 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq4030
       have i₂ := eq3514 sF2
       grind)
    | exact superpose eq3514 eq4030
    | exact resolve eq4030 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030
  have eq4072 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq4028
       have i₂ := eq3514 x
       grind)
    | exact superpose eq3514 eq4028
    | exact resolve eq4028 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514 eq4028
  have eq4138 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq4072 eq133
    | exact resolve eq133 eq4072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq4072
  have eq4154 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq4138
    | exact resolve eq4138 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4138
  have eq4404 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4154 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq4154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4154
  have eq4405 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq4404
  have eq5681 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq4405 eq548
    | exact resolve eq548 eq4405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4405
  have eq5688 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq5681
  have eq24881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24881
    | exact resolve eq24881 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24881
  have eq24890 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24882
       have r₂ := eq28
       grind)
    | exact resolve eq24882 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24882
  have eq24893 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24890
    | exact resolve eq24890 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24890
  have eq24960 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24893 eq548
    | exact resolve eq548 eq24893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24893
  have eq24980 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24960
    | exact resolve eq24960 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24960
  have eq24981 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24980
  have eq25044 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq548 x x
       have i₂ := eq24981
       grind)
    | exact superpose eq24981 eq548
    | exact resolve eq548 eq24981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24981
  have eq25064 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25044
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25044
    | exact resolve eq25044 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25044
  have eq25065 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq25064
  have eq25074 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25065 eq28
    | exact resolve eq28 eq25065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25096 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25065 eq4070
    | exact resolve eq4070 eq25065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4070 eq25065
  have eq25149 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25096 eq116
    | exact resolve eq116 eq25096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq25096
  have eq25161 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq25149
  have eq25168 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq25161
       have r₂ := eq25074
       grind)
    | exact resolve eq25161 eq25074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25074 eq25161
  have eq25481 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq548 x x
       have i₂ := eq25168
       grind)
    | exact superpose eq25168 eq548
    | exact resolve eq548 eq25168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq25168
  have eq25501 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25481
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25481
    | exact resolve eq25481 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25481
  have eq25502 : y = (M.op x y) := by grind
  clear eq25501
  have eq25511 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq25502 eq21
    | exact resolve eq21 eq25502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25502
  have eq25647 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25511
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25511
    | exact resolve eq25511 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq25511
  have eq25666 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq25647 eq27
    | exact resolve eq27 eq25647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25647
  have eq25769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5688 eq25666
    | exact resolve eq25666 eq5688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5688 eq25666
  have eq25783 : False := by grind
  exact eq25783

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq75 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq131 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq140 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq212 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq208 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq208
    | (have j0 := eq208 X0
       grind)
    | exact resolve eq208 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq463 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x X0 X1 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq474 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq474
    | exact resolve eq474 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq479 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq465
    | (have j0 := eq465 X0 X1
       grind)
    | exact resolve eq465 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq481 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq463 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq463
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq487 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq478 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq478
    | (have j0 := eq478 x y
       grind)
    | exact resolve eq478 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (M.op X2 (M.op (M.op X2 (σ X0)) X3)) (σ (k X0 X1))) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (σ X0) X2 X3 (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq53
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq53 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq615 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq614 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq777 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    grind
  clear eq76
  have eq778 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq777 X0 X1 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq777
    | (have j0 := eq777 X0 X1 X2
       grind)
    | exact resolve eq777 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq779 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq778 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq814 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X2 (M.op (M.op X2 X0) X3)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq779 (M.op X0 X1) (M.op X2 (M.op (M.op X2 X0) X3)) X0
       have i₂ := eq53 X0 X2 X3 X1
       grind)
    | exact superpose eq53 eq779
    | exact resolve eq779 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq831 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq814 X0 X1 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq814
    | exact resolve eq814 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq903 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq831 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq831
    | (have j0 := eq831 x y
       grind)
    | exact resolve eq831 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq903 eq129
    | exact resolve eq129 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq918
    | exact resolve eq918 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq3066 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq479 eq53
    | exact resolve eq53 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3086 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3066 eq479
    | exact resolve eq479 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq3066
  have eq3185 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x X0
       have i₂ := eq481 X0 X0 x
       grind)
    | exact superpose eq481 eq53
    | exact resolve eq53 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3222 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq470 x x
       have i₂ := eq3185 x
       grind)
    | exact superpose eq3185 eq470
    | exact resolve eq470 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq3224 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq481 X0 X0 X0
       have i₂ := eq3185 X0
       grind)
    | exact superpose eq3185 eq481
    | exact resolve eq481 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3227 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X0 X0 X1
       have i₂ := eq3185 X0
       grind)
    | exact superpose eq3185 eq53
    | exact resolve eq53 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3277 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq615 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq615
    | (have j0 := eq615 (τ X0)
       grind)
    | exact resolve eq615 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq615
  have eq3285 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3277 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3277
    | (have j0 := eq3277 X0
       grind)
    | exact resolve eq3277 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3277
  have eq3291 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3285 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3285
    | (have j0 := eq3285 X0
       grind)
    | exact resolve eq3285 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq3309 : x = (k x (M.op (M.op x x) (M.op x y))) := by
    first
    | exact superpose eq3222 eq831
    | exact resolve eq831 eq3222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3222
  have eq3638 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3086 eq481
    | exact resolve eq481 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq3642 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3638 X0
       have i₂ := eq478 (M.op sF4 sF4) (M.op (M.op sF4 sF4) X0)
       grind)
    | (have i₁ := eq3638 x
       have i₂ := eq478 (M.op sF4 sF4) x
       grind)
    | exact superpose eq478 eq3638
    | exact resolve eq3638 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq8906 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) (k (σ (M.op x y)) (σ x))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq129 eq608
    | (have j0 := eq608 (M.op x y) x x x
       grind)
    | exact resolve eq608 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq608
  have eq9041 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) (k (σ (M.op x y)) (σ x))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq21 eq8906
    | (have j0 := eq8906 X0 X1
       grind)
    | exact resolve eq8906 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8906
  have eq9163 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq920 eq9041
    | exact resolve eq9041 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq9041
  have eq9255 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9163 x x
       have i₂ := eq14 sF1 x x
       grind)
    | exact superpose eq14 eq9163
    | exact resolve eq9163 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9163
  have eq9341 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq9255
    | exact resolve eq9255 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9255
  have eq9424 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9341
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9341
    | exact resolve eq9341 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9341
  have eq9501 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq9424
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9424
    | exact resolve eq9424 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9424
  have eq9512 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq9501
    | exact resolve eq9501 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9501
  have eq23733 : (σ x) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq3642 eq472
    | exact resolve eq472 eq3642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq3642
  have eq23799 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq23733
       have i₂ := eq3227 sF4 sF4
       grind)
    | exact superpose eq3227 eq23733
    | exact resolve eq23733 eq3227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23733
  have eq24180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq24180
    | exact resolve eq24180 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24180
  have eq24192 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24181
       have r₂ := eq28
       grind)
    | exact resolve eq24181 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24181
  have eq24225 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24192 eq478
    | exact resolve eq478 eq24192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24192
  have eq24234 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq24225
  have eq24267 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24234 eq831
    | exact resolve eq831 eq24234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq24234
  have eq24276 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24267 eq113
    | exact resolve eq113 eq24267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq24267
  have eq24289 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq24276
  have eq24520 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq478 y y
       have i₂ := eq24289
       grind)
    | exact superpose eq24289 eq478
    | exact resolve eq478 eq24289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24289
  have eq24529 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq24520
  have eq24848 : y = (M.op (M.op (M.op y y) x) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3227 y x
       have i₂ := eq24529
       grind)
    | exact superpose eq24529 eq3227
    | exact resolve eq3227 eq24529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227 eq24529
  have eq25859 : (M.op (M.op y y) x) = (M.op (M.op (M.op y y) y) (M.op (M.op y y) x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq481 (M.op y y) x y
       have i₂ := eq24848
       grind)
    | exact superpose eq24848 eq481
    | exact resolve eq481 eq24848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25892 : (M.op (M.op y y) x) = (M.op y (M.op (M.op y y) x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25859
       have i₂ := eq3185 y
       grind)
    | exact superpose eq3185 eq25859
    | exact resolve eq25859 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185 eq25859
  have eq80557 : (M.op y y) = (M.op (M.op (M.op y y) x) (M.op y y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq481 y y x
       have i₂ := eq25892
       grind)
    | exact superpose eq25892 eq481
    | exact resolve eq481 eq25892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25892
  have eq122901 : x = (M.op (M.op (M.op y y) (M.op y y)) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14 x (M.op y y) (M.op y y)
       have i₂ := eq80557
       grind)
    | exact superpose eq80557 eq14
    | exact resolve eq14 eq80557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80557
  have eq122966 : x = (M.op (M.op y y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq122901
       have i₂ := eq3224 y
       grind)
    | exact superpose eq3224 eq122901
    | exact resolve eq122901 eq3224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3224 eq122901
  have eq123020 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24848
       have i₂ := eq122966
       grind)
    | exact superpose eq122966 eq24848
    | exact resolve eq24848 eq122966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24848 eq122966
  have eq123122 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq123020
  have eq123139 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq123122
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq123122
    | exact resolve eq123122 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123122
  have eq123142 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123139 eq29
    | exact resolve eq29 eq123139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123147 : (k x x) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123139 eq50
    | exact resolve eq50 eq123139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq123154 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123139 eq62
    | exact resolve eq62 eq123139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq123161 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123139 eq140
    | exact resolve eq140 eq123139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq123139
  have eq123361 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq154 eq123161
    | exact resolve eq123161 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123161
  have eq123365 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq154 eq123154
    | exact resolve eq123154 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123154
  have eq123371 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq154 eq123147
    | exact resolve eq123147 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123147
  have eq123376 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq123142
    | exact resolve eq123142 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq123142
  have eq123377 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq903 eq123361
    | exact resolve eq123361 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq123361
  have eq127006 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123377 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq123377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127007 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq127006
  have eq129634 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  have eq129659 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq127007 eq481
    | exact resolve eq481 eq127007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127007
  have eq129686 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq212 eq129659
    | exact resolve eq129659 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq129659
  have eq135561 : (σ (k x (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123365 eq131
    | exact resolve eq131 eq123365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq123365
  have eq135617 : (k (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq46 eq135561
    | exact resolve eq135561 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135561
  have eq136136 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123371 eq123377
    | exact resolve eq123377 eq123371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123371 eq123377
  have eq136154 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by grind
  clear eq136136
  have eq136366 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3291 x
       have i₂ := eq136154
       grind)
    | exact superpose eq136154 eq3291
    | (have j0 := eq3291 x
       grind)
    | exact resolve eq3291 eq136154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291 eq136154
  have eq136386 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq136366
       have r₂ := eq123376
       grind)
    | exact resolve eq136366 eq123376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123376 eq136366
  have eq136425 : x = (k x (M.op x (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3309
       have i₂ := eq136386
       grind)
    | exact superpose eq136386 eq3309
    | exact resolve eq3309 eq136386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309 eq136386
  have eq136591 : x = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq487 eq136425
    | exact resolve eq136425 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq136425
  have eq137029 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq136591 eq46
    | exact resolve eq46 eq136591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq136591
  have eq137070 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq137029
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq137029
    | exact resolve eq137029 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq137029
  have eq142186 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135617 eq137070
    | exact resolve eq137070 eq135617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135617 eq137070
  have eq142194 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq142186
  have eq142214 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq142194 eq154
    | exact resolve eq154 eq142194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq142194
  have eq142262 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq142214
    | exact resolve eq142214 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq142214
  have eq144385 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129634 eq142262
    | exact resolve eq142262 eq129634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129634 eq142262
  have eq144401 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq144385
  have eq144600 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129686 eq14
    | exact resolve eq14 eq129686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129686
  have eq170910 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq144401 eq144600
    | exact resolve eq144600 eq144401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144401 eq144600
  have eq171075 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq170910 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170910
  have eq171929 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq171075 y
       grind)
    | exact superpose eq171075 eq19
    | (have j1 := eq171075 y
       grind)
    | exact resolve eq19 eq171075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq171075
  have eq172061 : y = (M.op x y) := by grind
  clear eq171929
  have eq172084 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq172061 eq21
    | exact resolve eq21 eq172061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq172061
  have eq172551 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq172084
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq172084
    | exact resolve eq172084 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq172084
  have eq172553 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq172551 eq27
    | exact resolve eq27 eq172551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq172557 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq172551 eq52
    | exact resolve eq52 eq172551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq172551
  have eq173814 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq23799 eq172557
    | exact resolve eq172557 eq23799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23799 eq172557
  have eq173908 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq9512 eq173814
    | exact resolve eq173814 eq9512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9512 eq173814
  have eq173980 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq173908
  have eq174014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq172553 eq173980
    | exact resolve eq173980 eq172553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173980
  have eq174024 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq174014
       have r₂ := eq28
       grind)
    | exact resolve eq174014 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174014
  have eq174066 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq174024 eq481
    | exact resolve eq481 eq174024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq174098 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq174066 X0
       have i₂ := eq478 sF1 (M.op sF1 X0)
       grind)
    | (have i₁ := eq174066 x
       have i₂ := eq478 sF1 x
       grind)
    | exact superpose eq478 eq174066
    | exact resolve eq174066 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq174066
  have eq175571 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq174098 eq14
    | exact resolve eq14 eq174098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175665 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq174024 eq175571
    | exact resolve eq175571 eq174024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174024 eq175571
  have eq176623 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq175665 eq174098
    | exact resolve eq174098 eq175665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174098 eq175665
  have eq179022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq176623 eq172553
    | exact resolve eq172553 eq176623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172553 eq176623
  have eq179143 : False := by grind
  exact eq179143

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 : G, (M.op (M.op X0 (k (M.op X0 X0) X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq559 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) X1)) := by
    intro X1
    first
    | exact superpose eq175 eq557
    | exact resolve eq557 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq808 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq821 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq824 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq864 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq821
       grind)
    | exact superpose eq821 eq39
    | exact resolve eq39 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq900
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq900
    | exact resolve eq900 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq903 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq901
    | exact resolve eq901 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq903 eq824
    | exact resolve eq824 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq911
       have r₂ := eq27
       grind)
    | exact resolve eq911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq923 : (σ x) = (M.op (M.op (σ x) (k (σ y) (σ x))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq918 eq543
    | exact resolve eq543 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq924 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq918 eq178
    | exact resolve eq178 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq931 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq903 eq924
    | exact resolve eq924 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq932 : (σ x) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq903 eq923
    | exact resolve eq923 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq923
  have eq934 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq931 eq559
    | exact resolve eq559 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq932 eq16
    | exact resolve eq16 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x X0 X1 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1225 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1220 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1220
    | exact resolve eq1220 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1371 : (σ x) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq918 eq956
    | exact resolve eq956 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq1384 : (σ x) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1371
  have eq1428 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1384 eq176
    | exact resolve eq176 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1429 : (σ y) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1384 eq16
    | exact resolve eq16 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1437 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq932 eq1429
    | exact resolve eq1429 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1438 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq932 eq1428
    | exact resolve eq1428 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932 eq1428
  have eq1441 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1437
    | exact resolve eq1437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1444 : (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq1441
       grind)
    | exact superpose eq1441 eq178
    | exact resolve eq178 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq1601 : (σ y) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq934 eq1438
    | exact resolve eq1438 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1614 : (σ y) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1601
  have eq1625 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1614 eq1384
    | exact resolve eq1384 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384 eq1614
  have eq1635 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1625
  have eq1708 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1635 eq1438
    | exact resolve eq1438 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438 eq1635
  have eq1719 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1708
  have eq1723 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq918 eq1719
    | exact resolve eq1719 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq1729 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1723 eq931
    | exact resolve eq931 eq1723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1740 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1723 eq16
    | exact resolve eq16 eq1723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq1743 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1729
  have eq1746 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq559 eq1740
    | exact resolve eq1740 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq1740
  have eq1845 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (σ y)) (M.op X0 X1)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq1746 eq176
    | exact resolve eq176 eq1746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1746 eq16
    | exact resolve eq16 eq1746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq1859 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq931 eq1846
    | exact resolve eq1846 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq1860 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op X0 X1)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq931 eq1845
    | exact resolve eq1845 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq1845
  have eq1866 : ∀ X0 : G, y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1743 eq1859
    | exact resolve eq1859 eq1743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq1867 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op X0 X1)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq1743 eq1860
    | exact resolve eq1860 eq1743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743 eq1860
  have eq1869 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq1866 eq1867
    | exact resolve eq1867 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866 eq1867
  have eq1956 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1869 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1869
    | (have j0 := eq1869 x y
       grind)
    | exact resolve eq1869 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1979 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq1869 X0 X1
       grind)
    | exact superpose eq1869 eq16
    | exact resolve eq16 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq2113 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq1979 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1979 eq178
    | exact resolve eq178 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq2913 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq2113 sF2
       grind)
    | exact superpose eq2113 eq141
    | exact resolve eq141 eq2113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq2929 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq918 eq2913
    | exact resolve eq2913 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq2913
  have eq2936 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq2929
    | exact resolve eq2929 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq2939 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2936
       have r₂ := eq808
       grind)
    | exact resolve eq2936 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq2936
  have eq2943 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq821
       have i₂ := eq2939
       grind)
    | exact superpose eq2939 eq821
    | exact resolve eq821 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq2956 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq2939
       grind)
    | exact superpose eq2939 eq39
    | exact resolve eq39 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939
  have eq2972 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2943
  have eq2976 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2956
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2956
    | exact resolve eq2956 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956
  have eq2984 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2976 eq824
    | exact resolve eq824 eq2976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq2990 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq2984
  have eq5215 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1225 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1225
    | (have j0 := eq1225 x y
       grind)
    | exact resolve eq1225 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5220 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1225 x x
       have i₂ := eq2972
       grind)
    | exact superpose eq2972 eq1225
    | exact resolve eq1225 eq2972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2972
  have eq5250 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2990 eq1225
    | exact resolve eq1225 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2990
  have eq5314 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq5250
    | exact resolve eq5250 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5250
  have eq5315 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5314
  have eq5321 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5220
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5220
    | exact resolve eq5220 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5220
  have eq5322 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5321
  have eq5352 : ∀ X0 : G, x = (M.op (M.op (M.op x (M.op y X0)) (M.op x y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq1205 x X0
       have i₂ := eq1956
       grind)
    | exact superpose eq1956 eq1205
    | exact resolve eq1205 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq5381 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) x) (M.op (M.op x y) X2)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1205 eq176
    | exact resolve eq176 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5399 : ∀ X2 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X2)) (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq5381 x x X2
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq5381
    | exact resolve eq5381 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5381
  have eq5413 : ∀ X0 : G, x = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq5322 eq5352
    | exact resolve eq5352 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5352
  have eq5435 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq5399 eq5413
    | exact resolve eq5413 eq5399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5399 eq5413
  have eq5436 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5435
  have eq5443 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5322 eq175
    | exact resolve eq175 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5449 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5443 X0
       have i₂ := eq1225 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq5443 x
       have i₂ := eq1225 sF2 x
       grind)
    | exact superpose eq1225 eq5443
    | exact resolve eq5443 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5443
  have eq5453 : y = (M.op (M.op x x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5436 eq174
    | exact resolve eq174 eq5436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5436
  have eq5471 : (M.op x y) = (M.op (M.op x x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5322 eq5453
    | exact resolve eq5453 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5453
  have eq5516 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5471
       have i₂ := eq5315
       grind)
    | exact superpose eq5315 eq5471
    | exact resolve eq5471 eq5315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5315 eq5471
  have eq5542 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5516
  have eq5564 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5322 eq5542
    | exact resolve eq5542 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5542
  have eq5618 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5449
    | (have j0 := eq5449 (σ y)
       grind)
    | exact resolve eq5449 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5633 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5449 eq176
    | exact resolve eq176 eq5449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq5634 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5449 eq16
    | exact resolve eq16 eq5449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5449
  have eq5654 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq5634
    | (have j0 := eq5634 X0
       grind)
    | exact resolve eq5634 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5634
  have eq5655 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq5633
    | (have j0 := eq5633 X0 X1
       grind)
    | exact resolve eq5633 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5633
  have eq5661 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5322 eq5618
    | exact resolve eq5618 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5618
  have eq5662 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5322 eq5654
    | exact resolve eq5654 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5654
  have eq5663 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5322 eq5655
    | exact resolve eq5655 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5655
  have eq5667 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5661
    | exact resolve eq5661 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5661
  have eq5668 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5662 eq5663
    | exact resolve eq5663 eq5662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5663
  have eq5672 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5322 eq5667
    | exact resolve eq5667 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667
  have eq5677 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5672 eq31
    | exact resolve eq31 eq5672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5672
  have eq5776 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq5677
    | exact resolve eq5677 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5677
  have eq5795 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1444
       have i₂ := eq5776
       grind)
    | exact superpose eq5776 eq1444
    | exact resolve eq1444 eq5776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444 eq5776
  have eq5852 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq5795
  have eq5909 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5322 eq5852
    | exact resolve eq5852 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5322 eq5852
  have eq5910 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5909
  have eq5930 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5564 eq5910
    | exact resolve eq5910 eq5564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5564 eq5910
  have eq6037 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5662 eq178
    | exact resolve eq178 eq5662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6093 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5662 eq6037
    | exact resolve eq6037 eq5662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5662 eq6037
  have eq6153 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6093 eq141
    | exact resolve eq141 eq6093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq6093
  have eq6182 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq6153
    | exact resolve eq6153 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6153
  have eq6324 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq864 x x
       have i₂ := eq6182
       grind)
    | exact superpose eq6182 eq864
    | (have j0 := eq864 x x
       grind)
    | (have r₁ := eq864 x x
       have r₂ := eq6182
       grind)
    | exact resolve eq864 eq6182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq6182
  have eq6325 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6324
  have eq6326 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6325
  have eq6610 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq5668 X0 X1
       grind)
    | exact superpose eq5668 eq16
    | exact resolve eq16 eq5668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668
  have eq7471 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6610 x X0
       have i₂ := eq6326
       grind)
    | exact superpose eq6326 eq6610
    | exact resolve eq6610 eq6326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6326 eq6610
  have eq7558 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7471 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7471
  have eq7638 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7558 y
       grind)
    | exact superpose eq7558 eq18
    | (have j1 := eq7558 y
       grind)
    | exact resolve eq18 eq7558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7558
  have eq7680 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq7638
  have eq7722 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq7680
       grind)
    | exact superpose eq7680 eq24
    | exact resolve eq24 eq7680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7680
  have eq7813 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq7722
    | exact resolve eq7722 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7722
  have eq8429 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5930 eq39
    | exact resolve eq39 eq5930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5930
  have eq8432 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8429
    | exact resolve eq8429 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8429
  have eq8434 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7813 eq8432
    | exact resolve eq8432 eq7813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8432
  have eq8558 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8434 eq824
    | exact resolve eq824 eq8434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq8434
  have eq8564 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8558
  have eq8826 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8564 eq1225
    | exact resolve eq1225 eq8564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8564
  have eq8850 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8826
    | exact resolve eq8826 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8826
  have eq8851 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8850
  have eq8855 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8851 eq27
    | exact resolve eq27 eq8851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8851
  have eq8875 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8855
       have r₂ := eq7813
       grind)
    | exact resolve eq8855 eq7813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8855
  have eq8880 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8875 eq27
    | exact resolve eq27 eq8875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8881 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8875 eq175
    | exact resolve eq175 eq8875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq8885 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8875 eq1211
    | exact resolve eq1211 eq8875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq8888 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8885 x x
       have i₂ := eq16 sF2 x x
       grind)
    | exact superpose eq16 eq8885
    | exact resolve eq8885 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8885
  have eq8890 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8881 X0
       have i₂ := eq1225 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq8881 x
       have i₂ := eq1225 sF2 x
       grind)
    | exact superpose eq1225 eq8881
    | exact resolve eq8881 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq8881
  have eq8963 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7813 eq8880
    | exact resolve eq8880 eq7813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7813 eq8880
  have eq8966 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq8963
  have eq9251 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8888 eq8890
    | exact resolve eq8890 eq8888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8888 eq8890
  have eq9300 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9251
  have eq9313 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9300
    | exact resolve eq9300 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9300
  have eq9321 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8875 eq9313
    | exact resolve eq9313 eq8875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8875 eq9313
  have eq9327 : x = (M.op x y) := by
    first
    | (have r₁ := eq9321
       have r₂ := eq8966
       grind)
    | exact resolve eq9321 eq8966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8966 eq9321
  have eq9331 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq18
    | exact resolve eq18 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9332 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq22
    | exact resolve eq22 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq9338 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op x y)) X1)) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1205 X0 X1
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq1205
    | exact resolve eq1205 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq9327
  have eq9354 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq9338 x x
       have i₂ := eq16 sF0 x x
       grind)
    | exact superpose eq16 eq9338
    | exact resolve eq9338 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9338
  have eq9359 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9332 eq20
    | exact resolve eq20 eq9332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9505 : y = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq9331 eq174
    | exact resolve eq174 eq9331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq9529 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq5215 eq9505
    | exact resolve eq9505 eq5215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5215 eq9505
  have eq9535 : y = (M.op x y) := by
    first
    | exact superpose eq9331 eq9529
    | exact resolve eq9529 eq9331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9331 eq9529
  have eq9538 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9535
       grind)
    | exact superpose eq9535 eq24
    | exact resolve eq24 eq9535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9535
  have eq9597 : (σ x) = (σ y) := by
    first
    | exact superpose eq9332 eq9538
    | exact resolve eq9538 eq9332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9332 eq9538
  have eq9614 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9597 eq26
    | exact resolve eq26 eq9597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9597
  have eq9735 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9354 eq178
    | exact resolve eq178 eq9354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq9762 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9354 eq9735
    | exact resolve eq9735 eq9354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9354 eq9735
  have eq9770 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq9762 eq37
    | exact resolve eq37 eq9762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq9762
  have eq9781 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq9770
    | exact resolve eq9770 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9770
  have eq9783 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq9359 eq9781
    | exact resolve eq9781 eq9359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9781
  have eq9855 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9614 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9614
  have eq9870 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9855
  have eq9878 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9783 eq9870
    | exact resolve eq9870 eq9783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9783 eq9870
  have eq9879 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9878
  have eq9884 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq9879 eq27
    | exact resolve eq27 eq9879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9879
  have eq9895 : False := by grind
  exact eq9895

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
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
  have eq449 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq49 X0 X1 X2 X3
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq49 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq49
    | (have j0 := eq49 x X0 X1 y
       grind)
    | exact resolve eq49 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq49 X0 X1 X2 X3
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq469 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq469
    | exact resolve eq469 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq475 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq458 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq458
    | exact resolve eq458 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq481 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq472 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq472
    | (have j0 := eq472 x y
       grind)
    | exact resolve eq472 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq472
    | (have j0 := eq472 (σ x) (σ y)
       grind)
    | exact resolve eq472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq3311 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 X0 x X0
       have i₂ := eq475 X0 X0 x
       grind)
    | exact superpose eq475 eq49
    | exact resolve eq49 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3352 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq475 X0 X0 X0
       have i₂ := eq3311 X0
       grind)
    | exact superpose eq3311 eq475
    | exact resolve eq475 eq3311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq3548 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) x) (M.op (M.op x y) X2)) (M.op (M.op x y) X3)) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq465 eq449
    | exact resolve eq449 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq465
  have eq3653 : ∀ X2 X3 : G, (M.op x y) = (M.op (M.op (M.op x (M.op (M.op x y) X2)) (M.op (M.op x y) X3)) (M.op x y)) := by
    intro X2 X3
    first
    | (have i₁ := eq3548 x x X2 X3
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq3548
    | exact resolve eq3548 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3548
  have eq3762 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  clear eq3352
  have eq12869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12869
    | exact resolve eq12869 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12869
  have eq12881 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12870
       have r₂ := eq28
       grind)
    | exact resolve eq12870 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12870
  have eq12883 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12881
    | exact resolve eq12881 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12881
  have eq12891 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq12907 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12883 eq472
    | exact resolve eq472 eq12883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12883
  have eq12910 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12907
    | exact resolve eq12907 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12907
  have eq12922 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12910
  have eq13353 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq12922
       grind)
    | exact superpose eq12922 eq85
    | exact resolve eq85 eq12922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq12922
  have eq13375 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13353
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13353
    | exact resolve eq13353 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13353
  have eq15147 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13375 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq13375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13375
  have eq15155 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15147
    | exact resolve eq15147 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15147
  have eq15156 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15155
  have eq15168 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq15156
    | exact resolve eq15156 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15156
  have eq15169 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15168
  have eq15315 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15169 eq472
    | exact resolve eq472 eq15169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15169
  have eq15321 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq15315
    | exact resolve eq15315 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15315
  have eq15322 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15321
  have eq15323 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15322 eq28
    | exact resolve eq28 eq15322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15322
  have eq16213 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12891 eq98
    | exact resolve eq98 eq12891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12891
  have eq16226 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16213
  have eq16234 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16226
       have r₂ := eq15323
       grind)
    | exact resolve eq16226 eq15323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16226
  have eq16265 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq472 x x
       have i₂ := eq16234
       grind)
    | exact superpose eq16234 eq472
    | exact resolve eq472 eq16234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16234
  have eq16271 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16265
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16265
    | exact resolve eq16265 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16265
  have eq16276 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16271 eq48
    | exact resolve eq48 eq16271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16285 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16271 eq483
    | exact resolve eq483 eq16271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16305 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16276 X0
       have i₂ := eq472 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq16276 x
       have i₂ := eq472 sF2 x
       grind)
    | exact superpose eq472 eq16276
    | exact resolve eq16276 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16276
  have eq18010 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16285 eq16305
    | exact resolve eq16305 eq16285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16285 eq16305
  have eq18064 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18010
  have eq18082 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq18064
    | exact resolve eq18064 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18064
  have eq18090 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18082 eq28
    | exact resolve eq28 eq18082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18111 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18082 eq16271
    | exact resolve eq16271 eq18082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16271
  have eq18120 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18111
  have eq18126 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18120 eq27
    | exact resolve eq27 eq18120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18120
  have eq19128 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18126
  have eq19600 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18082 eq19128
    | exact resolve eq19128 eq18082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18082 eq19128
  have eq19614 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19600
  have eq19846 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19614 eq98
    | exact resolve eq98 eq19614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq19614
  have eq19859 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq19846
  have eq19869 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19859
       have r₂ := eq18090
       grind)
    | exact resolve eq19859 eq18090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18090 eq19859
  have eq20357 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq472 x x
       have i₂ := eq19869
       grind)
    | exact superpose eq19869 eq472
    | exact resolve eq472 eq19869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19869
  have eq20365 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20357
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20357
    | exact resolve eq20357 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20357
  have eq20366 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq20365
  have eq20514 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20366 eq21
    | exact resolve eq21 eq20366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20366
  have eq20640 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20514
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20514
    | exact resolve eq20514 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20514
  have eq20717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20640 eq15323
    | (have r₁ := eq15323
       have r₂ := eq20640
       grind)
    | exact resolve eq15323 eq20640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15323
  have eq20758 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20717
  have eq20759 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20758
  have eq20980 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20759 eq48
    | exact resolve eq48 eq20759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq20989 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20759 eq483
    | exact resolve eq483 eq20759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq20759
  have eq21022 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20980 X0
       have i₂ := eq472 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq20980 x
       have i₂ := eq472 sF2 x
       grind)
    | exact superpose eq472 eq20980
    | exact resolve eq20980 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20980
  have eq24564 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20989 eq21022
    | exact resolve eq21022 eq20989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20989 eq21022
  have eq24634 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24564
  have eq24657 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq24634
    | exact resolve eq24634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24634
  have eq24669 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24657 eq28
    | exact resolve eq28 eq24657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24657
  have eq24723 : x = (M.op x y) := by
    first
    | (have r₁ := eq24669
       have r₂ := eq20640
       grind)
    | exact resolve eq24669 eq20640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20640 eq24669
  have eq24727 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq24723 eq21
    | exact resolve eq21 eq24723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq24793 : x = (M.op x x) := by
    first
    | exact superpose eq24723 eq481
    | exact resolve eq481 eq24723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq24882 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24727
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24727
    | exact resolve eq24727 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24727
  have eq24972 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24882 eq27
    | exact resolve eq27 eq24882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq25148 : x = (k x x) := by
    first
    | (have i₁ := eq3762 x
       have i₂ := eq24793
       grind)
    | exact superpose eq24793 eq3762
    | exact resolve eq3762 eq24793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3762
  have eq25217 : ∀ X2 X3 : G, x = (M.op (M.op (M.op x (M.op x X2)) (M.op x X3)) x) := by
    intro X2 X3
    first
    | exact superpose eq24723 eq3653
    | exact resolve eq3653 eq24723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3653
  have eq25218 : ∀ X2 X3 : G, x = (M.op (M.op (M.op x X2) (M.op x X3)) x) := by
    intro X2 X3
    first
    | (have i₁ := eq25217 X2 X3
       have i₂ := eq472 x X2
       grind)
    | (have i₁ := eq25217 X2 X3
       have i₂ := eq472 x (M.op x X2)
       grind)
    | exact superpose eq472 eq25217
    | exact resolve eq25217 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq25217
  have eq25271 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq25218 (M.op (M.op x X0) x) X0
       have i₂ := eq475 x X0 x
       grind)
    | exact superpose eq475 eq25218
    | exact resolve eq25218 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq25218
  have eq25370 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq604 x x
       have i₂ := eq25148
       grind)
    | exact superpose eq25148 eq604
    | (have j0 := eq604 x x
       grind)
    | exact resolve eq604 eq25148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq25148
  have eq25373 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25370
  have eq25374 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25373
  have eq25385 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25374
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25374
    | exact resolve eq25374 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25374
  have eq25401 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24882 eq25385
    | exact resolve eq25385 eq24882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25385
  have eq25601 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq25271 X0
       grind)
    | exact superpose eq25271 eq14
    | exact resolve eq14 eq25271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25271
  have eq25659 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25601 X0
       have i₂ := eq24793
       grind)
    | exact superpose eq24793 eq25601
    | exact resolve eq25601 eq24793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24793 eq25601
  have eq25695 : y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq25659 y
       grind)
    | exact superpose eq25659 eq19
    | (have j1 := eq25659 y
       grind)
    | exact resolve eq19 eq25659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25659
  have eq25795 : x = y := by
    first
    | exact superpose eq24723 eq25695
    | exact resolve eq25695 eq24723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24723 eq25695
  have eq25857 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq25795
       grind)
    | exact superpose eq25795 eq25
    | exact resolve eq25 eq25795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq25795
  have eq26007 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25857
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25857
    | exact resolve eq25857 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq25857
  have eq26072 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24882 eq26007
    | exact resolve eq26007 eq24882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24882 eq26007
  have eq26312 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26072 eq24972
    | exact resolve eq24972 eq26072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24972 eq26072
  have eq26316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25401 eq26312
    | exact resolve eq26312 eq25401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25401 eq26312
  have eq26382 : False := by grind
  exact eq26382

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq181 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 X0
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq817 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq178
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq853 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq858 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq883 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq854 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq854
    | (have j0 := eq854 (σ X0)
       grind)
    | exact resolve eq854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1853 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1874 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1879 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1883 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1879 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1879
    | exact resolve eq1879 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq1889 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1853 X0 x x X3 X4
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1853
    | exact resolve eq1853 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq1936 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1883 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1883
    | (have j0 := eq1883 x y
       grind)
    | exact resolve eq1883 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1939 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1883
    | (have j0 := eq1883 (σ x) (σ y)
       grind)
    | exact resolve eq1883 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1967 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op (M.op x y) X1)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1936 eq176
    | exact resolve eq176 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1968 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1936 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1969 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1936 eq16
    | exact resolve eq16 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq1970 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq1968
       have r₂ := eq12 x x
       grind)
    | exact resolve eq1968 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968
  have eq1977 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1939 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1978 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1939 eq16
    | exact resolve eq16 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq1979 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq12 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq1977
       have r₂ := eq12 x (σ x)
       grind)
    | exact resolve eq1977 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq2022 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1979 eq141
    | exact resolve eq141 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq5219 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq832
       grind)
    | exact superpose eq832 eq39
    | exact resolve eq39 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq5220 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5219
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5219
    | exact resolve eq5219 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5219
  have eq5223 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq5220
    | exact resolve eq5220 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5220
  have eq15127 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0 x X0
       have i₂ := eq1889 X0 X0 x
       grind)
    | exact superpose eq1889 eq176
    | exact resolve eq176 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq15200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5223 eq842
    | exact resolve eq842 eq5223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842 eq5223
  have eq15208 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15200
       have r₂ := eq27
       grind)
    | exact resolve eq15200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15200
  have eq15230 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15208 eq1883
    | exact resolve eq1883 eq15208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15208
  have eq15235 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq15230
    | exact resolve eq15230 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15230
  have eq15250 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15235 eq178
    | exact resolve eq178 eq15235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15268 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15235 eq15250
    | exact resolve eq15250 eq15235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15235 eq15250
  have eq15276 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15268 eq141
    | exact resolve eq141 eq15268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15268
  have eq15284 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq15276
    | exact resolve eq15276 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15276
  have eq15289 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq854 x
       grind)
    | (have r₁ := eq15284
       have r₂ := eq854 x
       grind)
    | exact resolve eq15284 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15284
  have eq15295 : x = (M.op y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15127 x
       have i₂ := eq15289
       grind)
    | exact superpose eq15289 eq15127
    | exact resolve eq15127 eq15289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15300 : y = (k x x) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq15289
       grind)
    | exact superpose eq15289 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq15289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15308 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1883 x x
       have i₂ := eq15289
       grind)
    | exact superpose eq15289 eq1883
    | exact resolve eq1883 eq15289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15310 : x ≠ y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq15311 : y = (k x x) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15300
  have eq15313 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15308
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15308
    | exact resolve eq15308 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15308
  have eq15315 : y = (k x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15311
       have r₂ := eq15310
       grind)
    | exact resolve eq15311 eq15310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15310 eq15311
  have eq15318 : (M.op x y) = (k x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15313 eq15315
    | exact resolve eq15315 eq15313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15315
  have eq15337 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1889 x x x
       have i₂ := eq15313
       grind)
    | exact superpose eq15313 eq1889
    | exact resolve eq1889 eq15313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15341 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15337 X0
       have i₂ := eq1883 x X0
       grind)
    | (have i₁ := eq15337 X0
       have i₂ := eq1883 x (M.op x X0)
       grind)
    | exact superpose eq1883 eq15337
    | exact resolve eq15337 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15337
  have eq15457 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq854 x
       have i₂ := eq15318
       grind)
    | exact superpose eq15318 eq854
    | (have j0 := eq854 x
       grind)
    | exact resolve eq854 eq15318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq15460 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15457
  have eq15487 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq15341 X0
       grind)
    | exact superpose eq15341 eq16
    | exact resolve eq16 eq15341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15341
  have eq15503 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq15313 eq15487
    | exact resolve eq15487 eq15313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15313 eq15487
  have eq15559 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15503 y
       grind)
    | exact superpose eq15503 eq18
    | (have j1 := eq15503 y
       grind)
    | exact resolve eq18 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15503
  have eq15587 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15559
  have eq15612 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15587 eq1978
    | exact resolve eq1978 eq15587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1978
  have eq15614 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15587 eq2022
    | exact resolve eq2022 eq15587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022 eq15587
  have eq15616 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq15614
    | exact resolve eq15614 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15614
  have eq15994 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15616 eq178
    | exact resolve eq178 eq15616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15998 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15616 eq15127
    | exact resolve eq15127 eq15616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15127
  have eq16022 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15998 eq15612
    | exact resolve eq15612 eq15998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15612 eq15998
  have eq16038 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ y = (k y x) := by grind
  clear eq16022
  have eq16044 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq15616 eq16038
    | exact resolve eq16038 eq15616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15616 eq16038
  have eq16458 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15994 eq16044
    | exact resolve eq16044 eq15994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15994 eq16044
  have eq16483 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (k y x) := by grind
  clear eq16458
  have eq16497 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq16483 eq141
    | exact resolve eq141 eq16483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq16483
  have eq16499 : y = (k y x) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq31 eq16497
    | exact resolve eq16497 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq16497
  have eq16500 : y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq16499
  have eq16510 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq832
       have i₂ := eq16500
       grind)
    | exact superpose eq16500 eq832
    | exact resolve eq832 eq16500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq16500
  have eq16515 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq16510
  have eq16561 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1883 x x
       have i₂ := eq16515
       grind)
    | exact superpose eq16515 eq1883
    | exact resolve eq1883 eq16515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16515
  have eq16572 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16561
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16561
    | exact resolve eq16561 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16561
  have eq16573 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq16572
  have eq16602 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1889 x x x
       have i₂ := eq16573
       grind)
    | exact superpose eq16573 eq1889
    | exact resolve eq1889 eq16573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16610 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16602 X0
       have i₂ := eq1883 x X0
       grind)
    | (have i₁ := eq16602 X0
       have i₂ := eq1883 x (M.op x X0)
       grind)
    | exact superpose eq1883 eq16602
    | exact resolve eq16602 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16602
  have eq16718 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq16610 X0
       grind)
    | exact superpose eq16610 eq16
    | exact resolve eq16 eq16610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16610
  have eq16738 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16573 eq16718
    | exact resolve eq16718 eq16573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16573 eq16718
  have eq16794 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq858 x
       have i₂ := eq15318
       grind)
    | exact superpose eq15318 eq858
    | (have j0 := eq858 x
       grind)
    | exact resolve eq858 eq15318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq15318
  have eq16823 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16794
  have eq16904 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16738 y
       grind)
    | exact superpose eq16738 eq18
    | (have j1 := eq16738 y
       grind)
    | exact resolve eq18 eq16738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16738
  have eq16937 : y = (M.op x y) := by grind
  clear eq16904
  have eq16959 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq16937
       grind)
    | exact superpose eq16937 eq24
    | exact resolve eq24 eq16937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq16981 : x = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15295
       have i₂ := eq16937
       grind)
    | exact superpose eq16937 eq15295
    | exact resolve eq15295 eq16937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15295
  have eq16992 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16959 eq20
    | exact resolve eq20 eq16959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16959
  have eq22150 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x x) (M.op (M.op x y) X0)) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16981 eq1967
    | exact resolve eq1967 eq16981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq22152 : (M.op x y) = (M.op (M.op x x) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16981 eq1969
    | exact resolve eq1969 eq16981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969 eq16981
  have eq22178 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15289 eq22152
    | exact resolve eq22152 eq15289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22152
  have eq22179 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op (M.op x y) X0)) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq15289 eq22150
    | exact resolve eq22150 eq15289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15289 eq22150
  have eq22185 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22178
       have i₂ := eq16937
       grind)
    | exact superpose eq16937 eq22178
    | exact resolve eq22178 eq16937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22178
  have eq22186 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22179 X0
       have i₂ := eq16937
       grind)
    | exact superpose eq16937 eq22179
    | exact resolve eq22179 eq16937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16937 eq22179
  have eq22190 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq181 eq22186
    | exact resolve eq22186 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq22186
  have eq27763 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16823 eq22185
    | exact resolve eq22185 eq16823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22185
  have eq27802 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27763
  have eq27810 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1970 eq27802
    | exact resolve eq27802 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970 eq27802
  have eq27998 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22190 eq16
    | exact resolve eq16 eq22190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22190
  have eq28031 : ∀ X0 : G, (M.op (k (M.op x y) x) X0) = X0 ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16823 eq27998
    | exact resolve eq27998 eq16823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16823 eq27998
  have eq28063 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27810 eq28031
    | exact resolve eq28031 eq27810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27810 eq28031
  have eq28109 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28063 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28063
  have eq28131 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq28109 X0
       grind)
    | (have r₁ := eq28109 X0
       have r₂ := eq15460
       grind)
    | exact resolve eq28109 eq15460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15460 eq28109
  have eq28149 : ∀ X0 : G, (k x x) = (M.op x x) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq178 x
       have i₂ := eq28131 X0
       grind)
    | exact superpose eq28131 eq178
    | (have j1 := eq28131 X0
       grind)
    | exact resolve eq178 eq28131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28165 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op (M.op x y) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1889 x x x
       have i₂ := eq28131 X0
       grind)
    | exact superpose eq28131 eq1889
    | (have j1 := eq28131 X1
       grind)
    | exact resolve eq1889 eq28131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889
  have eq28174 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op (M.op x y) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq28165 X0 X1
       have i₂ := eq1883 x X0
       grind)
    | (have i₁ := eq28165 X0 X1
       have i₂ := eq1883 x (M.op x X0)
       grind)
    | exact superpose eq1883 eq28165
    | (have j0 := eq28165 X0 X1
       grind)
    | exact resolve eq28165 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883 eq28165
  have eq28182 : ∀ X0 : G, x = (k x x) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28131 eq28149
    | (have j0 := eq28149 X0
       have j1 := eq28131 X0
       grind)
    | exact resolve eq28149 eq28131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28149
  have eq28198 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq883 x
       have i₂ := eq28182 X0
       grind)
    | exact superpose eq28182 eq883
    | (have j0 := eq883 x
       have j1 := eq28182 X0
       grind)
    | exact resolve eq883 eq28182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28182
  have eq28204 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq28198 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28198
  have eq28208 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28204 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28204
    | (have j0 := eq28204 X0
       grind)
    | exact resolve eq28204 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28204
  have eq28614 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op x x) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1874 x x
       have i₂ := eq28174 sF2 x
       grind)
    | exact superpose eq28174 eq1874
    | (have j1 := eq28174 X0 X0
       grind)
    | exact resolve eq1874 eq28174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq28615 : ∀ X0 X1 : G, (M.op (M.op x x) X0) = X0 ∨ (M.op (M.op x y) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq28174 X0 X1
       grind)
    | exact superpose eq28174 eq16
    | (have j1 := eq28174 X0 X1
       grind)
    | exact resolve eq16 eq28174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28174
  have eq28651 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = X1 ∨ (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq28131 eq28615
    | (have j0 := eq28615 X0 X1
       have j1 := eq28131 X1
       grind)
    | exact resolve eq28615 eq28131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28615
  have eq28652 : ∀ X0 : G, (σ x) = (M.op (M.op x (M.op (σ x) (σ y))) (σ x)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28131 eq28614
    | (have j0 := eq28614 X0
       have j1 := eq28131 X0
       grind)
    | exact resolve eq28614 eq28131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28131 eq28614
  have eq28655 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28651 eq28652
    | (have j0 := eq28652 X0
       have j1 := eq28651 X0 X0
       grind)
    | exact resolve eq28652 eq28651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28651 eq28652
  have eq29240 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq28655 (M.op sF4 X0)
       grind)
    | exact superpose eq28655 eq175
    | (have j1 := eq28655 X0
       grind)
    | exact resolve eq175 eq28655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq28655
  have eq29272 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28208 eq29240
    | (have j0 := eq29240 X0
       have j1 := eq28208 X0
       grind)
    | exact resolve eq29240 eq28208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28208 eq29240
  have eq29274 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq29272
    | (have j0 := eq29272 X0
       grind)
    | exact resolve eq29272 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29272
  have eq29275 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29274 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29274
  have eq29296 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29275 eq178
    | exact resolve eq178 eq29275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq29322 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq29275 eq16
    | exact resolve eq16 eq29275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29347 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f29347_13 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f29347_14 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f29347_23 : X0 ≠ (M.op (M.op X0 X1) X0) := by grind
    have f29347_24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f29347_26 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f29347_14 X0
         grind)
      | (have r₁ := f29347_14 X0
         have r₂ := f29347_24
         grind)
      | exact resolve f29347_14 f29347_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f29347_27 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X0 := by
      intro X0 X1
      first
      | (have j0 := f29347_13 X0 X1
         grind)
      | (have r₁ := f29347_13 X0 X1
         have r₂ := f29347_24
         grind)
      | exact resolve f29347_13 f29347_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f29347_28 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f29347_27 X0 X1
         have i₂ := f29347_26 X0
         grind)
      | exact superpose f29347_26 f29347_27
      | exact resolve f29347_27 f29347_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f29347_31 : X0 ≠ X0 := by
      first
      | (have i₁ := f29347_23
         have i₂ := f29347_28 X0 X1
         grind)
      | exact superpose f29347_28 f29347_23
      | (have r₁ := f29347_23
         have r₂ := f29347_28 X0 X1
         grind)
      | exact resolve f29347_23 f29347_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f29347_32 : False := by grind
    exact f29347_32
  clear eq29322
  have eq29362 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29275 eq29296
    | exact resolve eq29296 eq29275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29275 eq29296
  have eq29385 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29362 eq883
    | (have j0 := eq883 (M.op x y)
       grind)
    | exact resolve eq883 eq29362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq29362
  have eq29391 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29385
  have eq29393 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq29391
    | exact resolve eq29391 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq29391
  have eq29403 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16992 eq29393
    | exact resolve eq29393 eq16992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29393
  have eq29786 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq29347 X0 X1
       grind)
    | exact superpose eq29347 eq16
    | exact resolve eq16 eq29347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30334 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29403 eq29786
    | exact resolve eq29786 eq29403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29403 eq29786
  have eq30409 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq30334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30334
  have eq30484 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30409 eq29347
    | exact resolve eq29347 eq30409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29347 eq30409
  have eq30500 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq30484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30484
  have eq30599 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30500 eq26
    | (have j1 := eq30500 (σ x)
       grind)
    | exact resolve eq26 eq30500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq30500
  have eq30622 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq30599
  have eq30643 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq30622 eq27
    | exact resolve eq27 eq30622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30622
  have eq30657 : False := by grind
  exact eq30657

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_pxy_pxx_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y x) ∨ x = (k x y) := by
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
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq97 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq104
    | exact resolve eq104 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq108
    | exact resolve eq108 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq133 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq134
       have i₂ := eq66 sF1
       grind)
    | exact superpose eq66 eq134
    | exact resolve eq134 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq139 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq66 sF0
       grind)
    | exact superpose eq66 eq137
    | exact resolve eq137 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq236 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq630 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq641 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4) (M.op (M.op X0 X1) (M.op X0 X2))) X5) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X1 X3 X3
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)
       have i₂ := eq52 (M.op (M.op X0 X1) (M.op X0 X2)) X0 X3 X4
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3 X2 X3
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq855 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq855
  have eq895 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq856 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq856
    | (have j0 := eq856 X0 y
       grind)
    | exact resolve eq856 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (σ X1) X2
       have i₂ := eq856 X0 X1
       grind)
    | exact superpose eq856 eq14
    | (have j1 := eq856 X0 X1
       grind)
    | exact resolve eq14 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq1077 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq653 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq653
    | (have j0 := eq653 x y X0
       grind)
    | exact resolve eq653 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1092 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq653 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq653
    | (have j0 := eq653 x X0 y
       grind)
    | exact resolve eq653 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1093 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq653
    | (have j0 := eq653 (σ x) X0 (σ y)
       grind)
    | exact resolve eq653 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq653 X0 X1 x
       grind)
    | exact superpose eq653 eq14
    | exact resolve eq14 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1166 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1097 (M.op X0 X1) X2
       have i₂ := eq653 X0 X1 X1
       grind)
    | exact superpose eq653 eq1097
    | exact resolve eq1097 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1170 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1097 X0 (M.op X0 X1)
       have i₂ := eq653 X0 X0 X1
       grind)
    | exact superpose eq653 eq1097
    | exact resolve eq1097 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1175 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1097 (M.op X0 X1) X0
       grind)
    | exact superpose eq1097 eq55
    | exact resolve eq55 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1180 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1097 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1097 eq14
    | exact resolve eq14 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1175 X0 X1
       have i₂ := eq653 X0 X1 X1
       grind)
    | exact superpose eq653 eq1175
    | exact resolve eq1175 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1277 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1092 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1092
    | (have j0 := eq1092 y
       grind)
    | exact resolve eq1092 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1314 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1277
       have i₂ := eq1077 X0
       grind)
    | exact superpose eq1077 eq1277
    | exact resolve eq1277 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1463 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1093
    | (have j0 := eq1093 (σ y)
       grind)
    | exact resolve eq1093 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1760 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1170 (M.op x x) y
       have i₂ := eq1277
       grind)
    | exact superpose eq1277 eq1170
    | exact resolve eq1170 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1764 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq236 eq1170
    | exact resolve eq1170 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1770 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq243 eq1170
    | exact resolve eq1170 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1801 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1770
       have i₂ := eq1097 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1097 eq1770
    | exact resolve eq1770 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq1807 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1764
       have i₂ := eq1097 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1097 eq1764
    | exact resolve eq1764 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq1811 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1760
       have i₂ := eq1097 x (M.op x x)
       grind)
    | exact superpose eq1097 eq1760
    | exact resolve eq1760 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq1760
  have eq1851 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1801 eq243
    | exact resolve eq243 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq1936 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1807 eq236
    | exact resolve eq236 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq1945 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1807 eq653
    | exact resolve eq653 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1960 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1945 x
       have i₂ := eq653 sF0 x x
       grind)
    | exact superpose eq653 eq1945
    | exact resolve eq1945 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq1964 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1807 eq1960
    | exact resolve eq1960 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq2134 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1807 eq1811
    | exact resolve eq1811 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq2846 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1195 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1195
    | exact resolve eq1195 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2854 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1195 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1170 X0 X1
       grind)
    | exact superpose eq1170 eq1195
    | exact resolve eq1195 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2874 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1180 X0 X1
       have i₂ := eq1195 X0 X1
       grind)
    | (have i₁ := eq1180 X1 X1
       have i₂ := eq1195 X1 X1
       grind)
    | exact superpose eq1195 eq1180
    | exact resolve eq1180 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2931 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2854 X0 X1
       have i₂ := eq1180 X0 X0
       grind)
    | exact superpose eq1180 eq2854
    | exact resolve eq2854 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq2854
  have eq2938 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2931 X0 X1
       have i₂ := eq653 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq653 eq2931
    | exact resolve eq2931 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931
  have eq2939 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2938 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2938
    | exact resolve eq2938 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq3400 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2939 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2939
    | (have j0 := eq2939 x y
       grind)
    | exact resolve eq2939 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3406 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2939
    | (have j0 := eq2939 (σ x) (σ y)
       grind)
    | exact resolve eq2939 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3541 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq3400 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq3400
       grind)
    | exact resolve eq12 eq3400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3400
  have eq3554 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by grind
  clear eq3541
  have eq3562 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3406 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq3406
       grind)
    | exact resolve eq12 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq3575 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq3562
  have eq3864 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2846 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2846 X0 X1
       grind)
    | exact superpose eq2846 eq2846
    | exact resolve eq2846 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3964 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3864 X0 X1
       have i₂ := eq1195 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1195 eq3864
    | exact resolve eq3864 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3864
  have eq3998 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3964 X0 X1
       have i₂ := eq653 X0 X0 X1
       grind)
    | exact superpose eq653 eq3964
    | exact resolve eq3964 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3964
  have eq4501 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1314 eq239
    | (have j0 := eq239 y X1
       grind)
    | exact resolve eq239 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq4502 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1807 eq4501
    | exact resolve eq4501 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4501
  have eq4518 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4502 eq2846
    | exact resolve eq2846 eq4502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4502
  have eq4524 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1936 eq4518
    | exact resolve eq4518 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518
  have eq4531 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq2134 eq4524
    | exact resolve eq4524 eq2134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134 eq4524
  have eq6244 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1170 X0 X2
       have i₂ := eq3998 X0 X1
       grind)
    | (have i₁ := eq1170 X1 X1
       have i₂ := eq3998 X1 X1
       grind)
    | exact superpose eq3998 eq1170
    | exact resolve eq1170 eq3998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq6245 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2874 X0 X0
       have i₂ := eq3998 X0 X1
       grind)
    | (have i₁ := eq2874 X1 X1
       have i₂ := eq3998 X1 X1
       grind)
    | exact superpose eq3998 eq2874
    | exact resolve eq2874 eq3998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874 eq3998
  have eq8422 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq895 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq895
    | (have j0 := eq895 x
       grind)
    | exact resolve eq895 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq8453 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8422
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq8422
    | exact resolve eq8422 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8422
  have eq8470 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq8453
    | exact resolve eq8453 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8453
  have eq8484 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8470
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq8470
    | exact resolve eq8470 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8470
  have eq8496 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq8484
    | exact resolve eq8484 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8484
  have eq8507 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq8496
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq8496
    | exact resolve eq8496 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8496
  have eq10502 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1314 eq632
    | (have j0 := eq632 y X1 X2
       grind)
    | exact resolve eq632 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq1314
  have eq10503 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1807 eq10502
    | exact resolve eq10502 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10502
  have eq10504 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4531 eq10503
    | exact resolve eq10503 eq4531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4531 eq10503
  have eq11579 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq10504 y
       have i₂ := eq1077 X0
       grind)
    | exact superpose eq1077 eq10504
    | exact resolve eq10504 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077 eq10504
  have eq11628 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq11579 x
       have i₂ := eq653 sF0 x (M.op x x)
       grind)
    | exact superpose eq653 eq11579
    | exact resolve eq11579 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11579
  have eq11648 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq11628
       have i₂ := eq1195 sF0 x
       grind)
    | exact superpose eq1195 eq11628
    | exact resolve eq11628 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11628
  have eq11662 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq1964 eq11648
    | exact resolve eq11648 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11648
  have eq16386 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4)) X1) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq630 X0 X1 x X3 X4
       have i₂ := eq653 X0 X1 x
       grind)
    | exact superpose eq653 eq630
    | exact resolve eq630 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq16645 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16386 X0 X1 X2 (M.op X0 x)
       have i₂ := eq653 X0 (M.op (M.op (M.op X0 X0) X1) X2) x
       grind)
    | exact superpose eq653 eq16386
    | exact resolve eq16386 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16386
  have eq16702 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16645 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq14 eq16645
    | exact resolve eq16645 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16645
  have eq17024 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq641 X0 X1 x X3 X4
       have i₂ := eq653 X0 X1 x
       grind)
    | exact superpose eq653 eq641
    | exact resolve eq641 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq17142 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17024 X0 (M.op X0 X1) X2 X2
       have i₂ := eq55 X0 X0 X1 X2
       grind)
    | exact superpose eq55 eq17024
    | exact resolve eq17024 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq17172 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) X3) X2
       have i₂ := eq17024 X0 X1 (M.op (M.op (M.op X0 X0) X1) X2) X3
       grind)
    | exact superpose eq17024 eq14
    | exact resolve eq14 eq17024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17024
  have eq17220 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17172 X0 X1 X2 x
       have i₂ := eq2939 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) x
       grind)
    | exact superpose eq2939 eq17172
    | exact resolve eq17172 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17172
  have eq17242 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17142 X0 X1 X2
       have i₂ := eq653 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq653 eq17142
    | exact resolve eq17142 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17142
  have eq17337 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17220 X0 X1 X2
       have i₂ := eq653 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0 X0
       grind)
    | exact superpose eq653 eq17220
    | exact resolve eq17220 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17220
  have eq17355 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17242 X0 X1 X2
       have i₂ := eq653 X0 X0 X0
       grind)
    | exact superpose eq653 eq17242
    | exact resolve eq17242 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17242
  have eq17412 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17337 X0 X1 X2
       have i₂ := eq1195 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0
       grind)
    | exact superpose eq1195 eq17337
    | exact resolve eq17337 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17337
  have eq17427 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17355 X0 X1 X2
       have i₂ := eq6244 X0 X0 X1
       grind)
    | exact superpose eq6244 eq17355
    | exact resolve eq17355 eq6244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6244 eq17355
  have eq17456 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17412 X0 X1 X1
       have i₂ := eq2939 (M.op (M.op X0 X0) X1) X1
       grind)
    | exact superpose eq2939 eq17412
    | exact resolve eq17412 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17412
  have eq17466 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq17427 X0 x X2
       have i₂ := eq653 X0 X0 x
       grind)
    | exact superpose eq653 eq17427
    | exact resolve eq17427 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17427
  have eq17484 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17456 X0 x
       have i₂ := eq653 (M.op X0 X0) x x
       grind)
    | exact superpose eq653 eq17456
    | exact resolve eq17456 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17456
  have eq17499 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op (M.op (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17484 x X1
       have i₂ := eq653 x x x
       grind)
    | exact superpose eq653 eq17484
    | exact resolve eq17484 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17484
  have eq18518 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) X0)) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq133 eq900
    | (have j0 := eq900 (M.op x y) y x
       grind)
    | exact resolve eq900 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq18660 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) X0)) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq18518 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18518
    | (have j0 := eq18518 X0
       grind)
    | exact resolve eq18518 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18518
  have eq18728 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) X0)) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq18660
    | (have j0 := eq18660 X0
       grind)
    | exact resolve eq18660 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18660
  have eq18781 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) X0)) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq18728 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18728
    | (have j0 := eq18728 X0
       grind)
    | exact resolve eq18728 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18728
  have eq18826 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) X0)) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq18781
    | (have j0 := eq18781 X0
       grind)
    | exact resolve eq18781 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18781
  have eq18867 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) X0)) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq139 eq18826
    | (have j0 := eq18826 X0
       grind)
    | exact resolve eq18826 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18826
  have eq18908 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq18867
    | (have j0 := eq18867 X0
       grind)
    | exact resolve eq18867 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18867
  have eq18943 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18908 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18908
    | (have j0 := eq18908 X0
       grind)
    | exact resolve eq18908 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq18908
  have eq18971 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) X0)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq139 eq18943
    | (have j0 := eq18943 X0
       grind)
    | exact resolve eq18943 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq18943
  have eq22297 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq771 X0 X1 X2 X3 x
       have i₂ := eq2939 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) x
       grind)
    | exact superpose eq2939 eq771
    | exact resolve eq771 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq22298 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0)) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22297 X0 X1 X2 X3
       have i₂ := eq653 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)
       grind)
    | exact superpose eq653 eq22297
    | exact resolve eq22297 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22297
  have eq22299 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op (M.op X0 X0) X1) X0)) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq22298 X0 X1 x X3
       have i₂ := eq653 X0 X1 x
       grind)
    | exact superpose eq653 eq22298
    | exact resolve eq22298 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22298
  have eq22300 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq22299 X0 X1 X3
       have i₂ := eq653 (M.op (M.op X0 X0) X1) X0 X0
       grind)
    | exact superpose eq653 eq22299
    | exact resolve eq22299 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22299
  have eq22301 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq22300 X0 X1 X3
       have i₂ := eq1195 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq1195 eq22300
    | exact resolve eq22300 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22300
  have eq26018 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4) (M.op (M.op X0 X0) X1)) X5) (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0)) X5) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq757 X0 X1 x X3 X4 X5
       have i₂ := eq653 X0 X1 x
       grind)
    | exact superpose eq653 eq757
    | exact resolve eq757 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq26976 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq775 X0 X1 x X3 X4 X5
       have i₂ := eq653 X0 X1 x
       grind)
    | exact superpose eq653 eq775
    | exact resolve eq775 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq27155 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) X2)) (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26018 X0 X1 (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) X2)) X3)
       have i₂ := eq26976 (M.op (M.op X0 X0) X1) X0 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) X2 X3
       grind)
    | exact superpose eq26976 eq26018
    | exact resolve eq26018 eq26976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26018 eq26976
  have eq27190 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) X2)) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27155 X0 X1 X2 x
       have i₂ := eq2939 (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) X2)) x
       grind)
    | exact superpose eq2939 eq27155
    | exact resolve eq27155 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939 eq27155
  have eq27326 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27190 X0 X1 X2
       have i₂ := eq653 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) X2) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op X0 X0) X1)) X2)
       grind)
    | exact superpose eq653 eq27190
    | exact resolve eq27190 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27190
  have eq27431 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27326 X0 X1 X2
       have i₂ := eq1195 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1195 eq27326
    | exact resolve eq27326 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27326
  have eq27508 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1))) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1))) (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27431 X1 X1 X2
       have i₂ := eq1195 (M.op (M.op X1 X1) X1) X1
       grind)
    | exact superpose eq1195 eq27431
    | exact resolve eq27431 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27431
  have eq27570 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) X0) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1))) (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27508 X0 X1 X2
       have i₂ := eq2846 (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq2846 eq27508
    | exact resolve eq27508 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27508
  have eq27604 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) X0) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op (M.op X0 X0) X1) X0)) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27570 X0 X1 X2
       have i₂ := eq653 (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq653 eq27570
    | exact resolve eq27570 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27570
  have eq27615 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) X0) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) X0)) (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27604 X0 X1 X2
       have i₂ := eq1195 (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1195 eq27604
    | exact resolve eq27604 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27604
  have eq27624 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) X0) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27615 X0 X1 X2
       have i₂ := eq22301 X0 X1 X0
       grind)
    | exact superpose eq22301 eq27615
    | exact resolve eq27615 eq22301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22301 eq27615
  have eq42909 : x = (M.op (M.op x x) y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq3554 eq1936
    | exact resolve eq1936 eq3554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936 eq3554
  have eq43017 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq42909
       have i₂ := eq1277
       grind)
    | exact superpose eq1277 eq42909
    | exact resolve eq42909 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq42909
  have eq43029 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1807 eq43017
    | exact resolve eq43017 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807 eq43017
  have eq43722 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X0) = (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17466 X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X1) X2)
       have i₂ := eq16702 (M.op (M.op X0 X0) X0) X1 X2
       grind)
    | exact superpose eq16702 eq17466
    | exact resolve eq17466 eq16702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16702
  have eq43895 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) X0) = (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43722 X2 X1 X2
       have i₂ := eq653 (M.op X2 X2) X2 X2
       grind)
    | exact superpose eq653 eq43722
    | exact resolve eq43722 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43722
  have eq43948 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    have f43948_11 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) X0) = (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) X1) X2)) := by
      intro X0 X1 X2
      grind
    have f43948_18 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
      intro X0 X1 X2
      grind
    have f43948_20 : (M.op X0 X0) ≠ (M.op X0 (M.op (M.op X0 X1) X2)) := by grind
    have f43948_21 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
      intro X0 X1 X2
      first
      | (have i₁ := f43948_11 X2 X1 X2
         have i₂ := f43948_18 X2 X2 X2
         grind)
      | exact superpose f43948_18 f43948_11
      | exact resolve f43948_11 f43948_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f43948_30 : (M.op X0 X0) ≠ (M.op X0 X0) := by
      first
      | (have i₁ := f43948_20
         have i₂ := f43948_21 X0 X1 X2
         grind)
      | exact superpose f43948_21 f43948_20
      | (have r₁ := f43948_20
         have r₂ := f43948_21 X0 X1 X2
         grind)
      | exact resolve f43948_20 f43948_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f43948_31 : False := by grind
    exact f43948_31
  clear eq43895
  have eq45532 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3575 eq1851
    | exact resolve eq1851 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851 eq3575
  have eq45630 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1463 eq45532
    | exact resolve eq45532 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463 eq45532
  have eq45643 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1801 eq45630
    | exact resolve eq45630 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801 eq45630
  have eq50728 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1166 X0 X1 X2
       have i₂ := eq1195 X0 X1
       grind)
    | (have i₁ := eq1166 X1 X1 X2
       have i₂ := eq1195 X1 X1
       grind)
    | exact superpose eq1195 eq1166
    | exact resolve eq1166 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75554 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x x) y) X0) X0) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq50728 y x x
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq50728
    | exact resolve eq50728 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq75946 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq75554 x
       have i₂ := eq1166 x y x
       grind)
    | exact superpose eq1166 eq75554
    | exact resolve eq75554 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75554
  have eq76186 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq75946
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75946
    | exact resolve eq75946 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq75946
  have eq76187 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq76186
  have eq76281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76187 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq76187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq76281
    | exact resolve eq76281 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76281
  have eq76301 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq76290
       have r₂ := eq27
       grind)
    | exact resolve eq76290 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76290
  have eq76305 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq76301
    | exact resolve eq76301 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76301
  have eq76335 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq76305 eq50728
    | exact resolve eq50728 eq76305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76305
  have eq76341 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq76335 x
       have i₂ := eq1166 sF2 sF3 x
       grind)
    | exact superpose eq1166 eq76335
    | exact resolve eq76335 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76335
  have eq76356 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq76341
    | exact resolve eq76341 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76341
  have eq76357 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq76356
  have eq76424 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76357 eq78
    | (have r₁ := eq78
       have r₂ := eq76357
       grind)
    | exact resolve eq78 eq76357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq76489 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq76357 eq13
    | exact resolve eq13 eq76357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76357
  have eq76565 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq76424
  have eq105608 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76565 eq76489
    | (have j0 := eq76489 (σ y)
       grind)
    | (have r₁ := eq76489 (σ y)
       have r₂ := eq76565
       grind)
    | exact resolve eq76489 eq76565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76489 eq76565
  have eq105637 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq105608
  have eq105638 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq105637
  have eq138468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76187 eq105638
    | exact resolve eq105638 eq76187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq105638 eq76187
    | exact resolve eq76187 eq105638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76187 eq105638
  have eq138493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq138479
  have eq138494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq138468
  have eq138496 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq138493
       have r₂ := eq27
       grind)
    | exact resolve eq138493 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138493
  have eq138497 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq138494
       have r₂ := eq27
       grind)
    | exact resolve eq138494 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138494
  have eq138499 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq138497
       grind)
    | exact superpose eq138497 eq72
    | exact resolve eq72 eq138497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138497
  have eq138728 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq138499
    | exact resolve eq138499 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138499
  have eq139512 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (k (σ x) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq138728 eq13
    | exact resolve eq13 eq138728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140334 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq138496 eq59
    | exact resolve eq59 eq138496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq138496
  have eq140365 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq140334
    | exact resolve eq140334 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140334
  have eq145482 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq140365
       grind)
    | exact superpose eq140365 eq72
    | exact resolve eq72 eq140365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145483 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq140365
       grind)
    | exact superpose eq140365 eq77
    | (have r₁ := eq77
       have r₂ := eq140365
       grind)
    | exact resolve eq77 eq140365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq140365
  have eq145631 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq145483
  have eq145632 : (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq145631
  have eq145713 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq145482
    | exact resolve eq145482 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq145482
  have eq158971 : y = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2846 y x
       have i₂ := eq145632
       grind)
    | exact superpose eq145632 eq2846
    | exact resolve eq2846 eq145632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846 eq145632
  have eq158995 : y = (M.op (M.op (M.op x y) x) x) ∨ x = (k x y) := by
    first
    | exact superpose eq1964 eq158971
    | exact resolve eq158971 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964 eq158971
  have eq208913 : (M.op y y) = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq158995 eq11662
    | exact resolve eq11662 eq158995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11662 eq158995
  have eq223796 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17499 X0 X1
       have i₂ := eq17466 X0 X1
       grind)
    | exact superpose eq17466 eq17499
    | exact resolve eq17499 eq17466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17466 eq17499
  have eq227998 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27624 X0 X1 x
       have i₂ := eq43948 (M.op (M.op X0 X0) X1) X0 x
       grind)
    | exact superpose eq43948 eq27624
    | exact resolve eq27624 eq43948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27624 eq43948
  have eq227999 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq227998 X0 X1
       have i₂ := eq653 (M.op X0 X0) X1 X1
       grind)
    | exact superpose eq653 eq227998
    | exact resolve eq227998 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227998
  have eq228000 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq227999 X0 X1
       have i₂ := eq653 X0 X0 X0
       grind)
    | exact superpose eq653 eq227999
    | exact resolve eq227999 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq227999
  have eq251609 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq208913
       grind)
    | exact superpose eq208913 eq110
    | exact resolve eq110 eq208913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq208913
  have eq251798 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq251609
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq251609
    | exact resolve eq251609 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251609
  have eq274934 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) X0) X0) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq251798 eq50728
    | exact resolve eq50728 eq251798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50728 eq251798
  have eq274948 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq274934 x
       have i₂ := eq1166 sF2 sF3 x
       grind)
    | exact superpose eq1166 eq274934
    | exact resolve eq274934 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166 eq274934
  have eq275006 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq274948
    | exact resolve eq274948 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274948
  have eq275131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq275006 eq145713
    | exact resolve eq145713 eq275006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145713 eq275006
  have eq275285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq275131
  have eq275347 : x = (k x y) := by
    first
    | (have r₁ := eq275285
       have r₂ := eq27
       grind)
    | exact resolve eq275285 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275285
  have eq275397 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq275347
       grind)
    | exact superpose eq275347 eq44
    | exact resolve eq44 eq275347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275347
  have eq275449 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq275397
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq275397
    | exact resolve eq275397 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275397
  have eq284286 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq8507 eq139512
    | (have j0 := eq139512 (σ x)
       grind)
    | exact resolve eq139512 eq8507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8507 eq139512
  have eq284358 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq284286
       have r₂ := eq138728
       grind)
    | exact resolve eq284286 eq138728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284286
  have eq284400 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq275449 eq284358
    | exact resolve eq284358 eq275449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284358
  have eq284401 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq284400
  have eq284423 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq275449 eq284401
    | exact resolve eq284401 eq275449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284401
  have eq284645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq284423 eq138728
    | exact resolve eq138728 eq284423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284423
  have eq284826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq284645
  have eq284897 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq284826
       have r₂ := eq27
       grind)
    | exact resolve eq284826 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284826
  have eq285030 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq284897 eq45643
    | exact resolve eq45643 eq284897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45643 eq284897
  have eq285316 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq285030
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq285030
    | exact resolve eq285030 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285030
  have eq285317 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq285316
  have eq286538 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq285317 eq138728
    | exact resolve eq138728 eq285317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138728 eq285317
  have eq286726 : (σ (M.op x y)) = (σ x) := by grind
  clear eq286538
  have eq287568 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq286726 eq26
    | exact resolve eq26 eq286726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq287569 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq286726 eq28
    | exact resolve eq28 eq286726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq287941 : x = (M.op x y) := by
    first
    | exact superpose eq30 eq287569
    | exact resolve eq287569 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq287569
  have eq287998 : (σ (k x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq287941 eq133
    | exact resolve eq133 eq287941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq288211 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq287941 eq43029
    | exact resolve eq43029 eq287941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43029 eq287941
  have eq288327 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq288211
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq288211
    | exact resolve eq288211 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq288211
  have eq288328 : x = (M.op x x) := by grind
  clear eq288327
  have eq288502 : (k (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq287998
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq287998
    | exact resolve eq287998 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq287998
  have eq288632 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq275449 eq288502
    | exact resolve eq288502 eq275449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275449 eq288502
  have eq288714 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq286726 eq288632
    | exact resolve eq288632 eq286726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288632
  have eq289629 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq288328
       grind)
    | exact superpose eq288328 eq72
    | exact resolve eq72 eq288328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq288328
  have eq289967 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq286726 eq289629
    | exact resolve eq289629 eq286726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289629
  have eq290057 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq289967
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq289967
    | exact resolve eq289967 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq289967
  have eq290124 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq286726 eq290057
    | exact resolve eq290057 eq286726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286726 eq290057
  have eq298260 : (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq290124 eq18971
    | exact resolve eq18971 eq290124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18971
  have eq298446 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq288714 eq298260
    | exact resolve eq298260 eq288714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288714 eq298260
  have eq298502 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq290124 eq298446
    | exact resolve eq298446 eq290124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298446
  have eq298503 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq298502
  have eq298535 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq287568 eq298503
    | exact resolve eq298503 eq287568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298503
  have eq298561 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq298535
       have r₂ := eq27
       grind)
    | exact resolve eq298535 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298535
  have eq301115 : (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq298561 eq223796
    | exact resolve eq223796 eq298561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223796
  have eq301116 : (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) (σ y))) := by
    first
    | (have i₁ := eq301115
       have i₂ := eq228000 sF3 sF1
       grind)
    | exact superpose eq228000 eq301115
    | exact resolve eq301115 eq228000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228000 eq301115
  have eq301146 : (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) = (M.op (σ (M.op x y)) (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq301116
       have i₂ := eq1195 sF3 sF1
       grind)
    | exact superpose eq1195 eq301116
    | exact resolve eq301116 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq301116
  have eq301166 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) (σ y)) (σ y))) := by
    first
    | exact superpose eq298561 eq301146
    | exact resolve eq301146 eq298561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298561 eq301146
  have eq301179 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq301166
       have i₂ := eq6245 sF1 sF3
       grind)
    | exact superpose eq6245 eq301166
    | exact resolve eq301166 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6245 eq301166
  have eq301185 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq287568 eq301179
    | exact resolve eq301179 eq287568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287568 eq301179
  have eq301190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq290124 eq301185
    | exact resolve eq301185 eq290124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290124 eq301185
  have eq301193 : False := by grind
  exact eq301193

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq33 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq50 X0 X1
       grind)
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq100 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq53 X1 X0
       grind)
    | (have r₁ := eq96 X1 X0
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq96 X1 X1
       have r₂ := eq53 X1 X1
       grind)
    | exact resolve eq96 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq96
  have eq236 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq100 (σ X1) (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 X1
       have i₂ := eq100 X1 X0
       grind)
    | exact superpose eq100 eq236
    | exact resolve eq236 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq236
  have eq245 : False := by grind
  exact eq245
