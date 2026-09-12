import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_y_pxy_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
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
  have eq40 : y = (τ (σ y)) := by
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
  have eq50 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq54 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq59 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq54 X0 X0 X0
       grind)
    | (have i₁ := eq58 X0
       have i₂ := eq54 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq54 eq58
    | (have j0 := eq58 X0
       grind)
    | exact resolve eq58 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq80 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq54 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y X0
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 X0 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 x) (M.op x x)
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq12
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq102 (σ X0)
       grind)
    | exact superpose eq102 eq15
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq111
    | exact resolve eq111 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq157 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq59 (τ X0)
       grind)
    | exact superpose eq59 eq50
    | (have j1 := eq59 (τ X0)
       grind)
    | exact resolve eq50 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq59
  have eq179 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op (σ (τ X0)) (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq157 X0
       have i₂ := eq112 (τ X0)
       grind)
    | exact superpose eq112 eq157
    | (have j0 := eq157 X0
       grind)
    | exact resolve eq157 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq181 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq179
    | (have j0 := eq179 X0
       grind)
    | exact resolve eq179 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq184 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq10
    | exact resolve eq10 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (σ (k X1 (M.op X0 X0))) = (k (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq15
    | exact resolve eq15 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 (M.op X0 X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq29
    | exact resolve eq29 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq190 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 (M.op X0 X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq32
    | exact resolve eq32 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq192 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq37
    | exact resolve eq37 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq231 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq184 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq184
    | exact resolve eq184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq366 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq401 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq366 X0 X1
       grind)
    | exact superpose eq366 eq10
    | (have j1 := eq366 X0 X1
       grind)
    | exact resolve eq10 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq419 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq401 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq401
    | (have j0 := eq401 X0 X1
       grind)
    | exact resolve eq401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq1607 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
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
  have eq1647 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1607 eq14
    | (have j0 := eq14 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq1650 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1647
       have i₂ := eq54 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1647
       have i₂ := eq54 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq54 eq1647
    | exact resolve eq1647 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1863 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq190
    | (have j0 := eq190 (M.op x y)
       grind)
    | exact resolve eq190 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq2241 : (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1863 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq14 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq2244 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2241
       have i₂ := eq54 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2241
       have i₂ := eq54 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq54 eq2241
    | exact resolve eq2241 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241
  have eq2367 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq192
    | (have j0 := eq192 (M.op x y)
       grind)
    | exact resolve eq192 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq3357 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1 X0
       have i₂ := eq54 X0 X0 X0
       grind)
    | exact superpose eq54 eq97
    | (have j0 := eq97 X0 X1 X0
       grind)
    | (have r₁ := eq97 x X1 x
       have r₂ := eq54 x x x
       grind)
    | exact resolve eq97 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq3358 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3357 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3363 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq3358
    | exact resolve eq3358 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3366 : y = (k (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq3358 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3358
    | (have j0 := eq3358 y x
       grind)
    | exact resolve eq3358 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3384 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3366 eq1650
    | exact resolve eq1650 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650 eq3366
  have eq3387 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3363 eq2244
    | exact resolve eq2244 eq3363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq3391 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3384
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3384
    | exact resolve eq3384 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384
  have eq3394 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq3387
    | exact resolve eq3387 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387
  have eq5723 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (τ X0) (M.op (τ X0) (τ X0))
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq54
    | (have j1 := eq181 X0
       grind)
    | exact resolve eq54 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq26724 : x = (M.op x y) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ x)) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq3363
       have i₂ := eq419 x (M.op sF0 sF0)
       grind)
    | exact superpose eq419 eq3363
    | (have j1 := eq419 x (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq3363 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq3363
  have eq27073 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq26724
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26724
    | exact resolve eq26724 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26724
  have eq27306 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq27073
       have i₂ := eq112 sF0
       grind)
    | exact superpose eq112 eq27073
    | exact resolve eq27073 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27073
  have eq27450 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq21 eq27306
    | exact resolve eq27306 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27306
  have eq27564 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27450
       have i₂ := eq112 sF0
       grind)
    | exact superpose eq112 eq27450
    | exact resolve eq27450 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27450
  have eq27617 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq27564
    | exact resolve eq27564 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27564
  have eq27665 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27617
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27617
    | exact resolve eq27617 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27617
  have eq27708 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27665
       have i₂ := eq54 sF1 sF1 sF1
       grind)
    | (have i₁ := eq27665
       have i₂ := eq54 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq54 eq27665
    | exact resolve eq27665 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27665
  have eq51666 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (σ X0) = (k (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5723 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5723
    | (have j0 := eq5723 (σ X0) X1
       grind)
    | exact resolve eq5723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5723
  have eq51684 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq51666 X0 X1
       have i₂ := eq186 X0 X0
       grind)
    | exact superpose eq186 eq51666
    | (have j0 := eq51666 X0 X1
       grind)
    | exact resolve eq51666 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq51666
  have eq60843 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq51684 X0 X1
       grind)
    | exact superpose eq51684 eq10
    | (have j1 := eq51684 X0 X1
       grind)
    | exact resolve eq10 eq51684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51684
  have eq61064 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq60843 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60843
    | (have j0 := eq60843 X0 X1
       grind)
    | exact resolve eq60843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60843
  have eq61333 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3358 X0 (M.op x X0)
       have i₂ := eq61064 X0 x
       grind)
    | exact superpose eq61064 eq3358
    | (have j1 := eq61064 X0 x
       grind)
    | exact resolve eq3358 eq61064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61064
  have eq61368 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq61333 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61333
  have eq97127 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq3391 eq55
    | exact resolve eq55 eq3391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq3391
  have eq97140 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq3394 eq54
    | exact resolve eq54 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3394
  have eq101914 : ∀ X0 : G, (σ y) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq97127 eq3358
    | (have j1 := eq97127 X0
       grind)
    | exact resolve eq3358 eq97127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97127
  have eq101921 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq101914 X0
       have i₂ := eq3358 sF1 sF1
       grind)
    | exact superpose eq3358 eq101914
    | (have j0 := eq101914 X0
       grind)
    | exact resolve eq101914 eq3358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101914
  have eq101922 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq101921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101921
  have eq103158 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq101922 eq54
    | exact resolve eq54 eq101922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq101922
  have eq103199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq97140 eq103158
    | exact resolve eq103158 eq97140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97140
  have eq103218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq103199
    | exact resolve eq103199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103199
  have eq103222 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq103218
       have r₂ := eq28
       grind)
    | exact resolve eq103218 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103218
  have eq103261 : (σ x) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq103222 eq3358
    | exact resolve eq3358 eq103222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103222
  have eq103272 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq103261
       have i₂ := eq3358 sF1 sF1
       grind)
    | exact superpose eq3358 eq103261
    | exact resolve eq103261 eq3358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103261
  have eq103273 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq103272
  have eq103306 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq103273 eq40
    | exact resolve eq40 eq103273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq103273
  have eq103362 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq103306
    | exact resolve eq103306 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103306
  have eq103370 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq103362 eq39
    | exact resolve eq39 eq103362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103362
  have eq103425 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq103370
    | exact resolve eq103370 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103370
  have eq103429 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103425 eq21
    | exact resolve eq21 eq103425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103430 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq103425 eq80
    | exact resolve eq80 eq103425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq103504 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq103509 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103429
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq103429
    | exact resolve eq103429 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103429
  have eq103537 : (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103509 eq2367
    | exact resolve eq2367 eq103509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367
  have eq103562 : (σ (M.op x y)) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103537
       have i₂ := eq61368 sF1
       grind)
    | exact superpose eq61368 eq103537
    | exact resolve eq103537 eq61368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61368 eq103537
  have eq104879 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103430 (M.op y x)
       have i₂ := eq103430 x
       grind)
    | exact superpose eq103430 eq103430
    | exact resolve eq103430 eq103430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103430
  have eq104896 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq104879
  have eq104921 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq112 y
       have i₂ := eq104896
       grind)
    | exact superpose eq104896 eq112
    | exact resolve eq112 eq104896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104896
  have eq104964 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104921
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq104921
    | exact resolve eq104921 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104921
  have eq105033 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103509 eq104964
    | exact resolve eq104964 eq103509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103509 eq104964
  have eq105089 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq105033
  have eq105189 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105089 eq231
    | exact resolve eq231 eq105089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq105089
  have eq105230 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq105189
    | exact resolve eq105189 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105189
  have eq112774 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105230 eq103562
    | exact resolve eq103562 eq105230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103562 eq105230
  have eq112831 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq112774
  have eq112891 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq103425 eq112831
    | exact resolve eq112831 eq103425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103425 eq112831
  have eq112999 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq112891
       have r₂ := eq103504
       grind)
    | exact resolve eq112891 eq103504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103504 eq112891
  have eq113005 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq112999
       have i₂ := eq102 y
       grind)
    | exact superpose eq102 eq112999
    | exact resolve eq112999 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112999
  have eq113008 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113005
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq113005
    | exact resolve eq113005 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113005
  have eq113010 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113008
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq113008
    | exact resolve eq113008 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq113008
  have eq113134 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq113010 eq3358
    | exact resolve eq3358 eq113010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113152 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113134
       have i₂ := eq102 sF1
       grind)
    | exact superpose eq102 eq113134
    | exact resolve eq113134 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113134
  have eq113673 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq113152 eq27708
    | exact resolve eq27708 eq113152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27708 eq113152
  have eq113727 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq113673
  have eq113750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq113727
    | exact resolve eq113727 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113727
  have eq113764 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq113750
       have r₂ := eq28
       grind)
    | exact resolve eq113750 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113750
  have eq114133 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq113764 eq3358
    | exact resolve eq3358 eq113764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358 eq113764
  have eq114144 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114133
       have i₂ := eq102 sF3
       grind)
    | exact superpose eq102 eq114133
    | exact resolve eq114133 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq114133
  have eq114794 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114144 eq113010
    | exact resolve eq113010 eq114144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113010 eq114144
  have eq114840 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq114794
  have eq114883 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114840 eq39
    | exact resolve eq39 eq114840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq114840
  have eq114947 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq114883
    | exact resolve eq114883 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq114883
  have eq114948 : x = (M.op x y) := by grind
  clear eq114947
  have eq114953 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq114948 eq21
    | exact resolve eq21 eq114948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq114962 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq114948 eq83
    | exact resolve eq83 eq114948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq114948
  have eq131545 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq114953
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq114953
    | exact resolve eq114953 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114953
  have eq132394 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq131545 eq23
    | exact resolve eq23 eq131545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq132395 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq131545 eq27
    | exact resolve eq27 eq131545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq131545
  have eq139495 : x = (M.op x x) := by
    first
    | (have i₁ := eq114962 (M.op x x)
       have i₂ := eq114962 x
       grind)
    | exact superpose eq114962 eq114962
    | exact resolve eq114962 eq114962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114962
  have eq139809 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq139495
       grind)
    | exact superpose eq139495 eq112
    | exact resolve eq112 eq139495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq139495
  have eq139943 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq139809
       have i₂ := eq132394
       grind)
    | exact superpose eq132394 eq139809
    | exact resolve eq139809 eq132394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132394 eq139809
  have eq140357 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq139943 eq103158
    | exact resolve eq103158 eq139943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103158
  have eq140659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq132395 eq140357
    | exact resolve eq140357 eq132395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140357
  have eq140681 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq140659
       have r₂ := eq28
       grind)
    | exact resolve eq140659 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140659
  have eq144797 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq140681 eq132395
    | exact resolve eq132395 eq140681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132395 eq140681
  have eq144918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq139943 eq144797
    | exact resolve eq144797 eq139943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139943 eq144797
  have eq145673 : False := by grind
  exact eq145673

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_x_pxy_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
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
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq80 eq53
    | exact resolve eq53 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq99 (σ X0)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq137 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq137
    | exact resolve eq137 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq137
  have eq212 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq10
    | exact resolve eq10 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq28
    | exact resolve eq28 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq218 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq31
    | exact resolve eq31 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq258 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq212 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq212
    | exact resolve eq212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq1235 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq119 X0 X1
       grind)
    | exact superpose eq119 eq10
    | (have j1 := eq119 X0 X1
       grind)
    | exact resolve eq10 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1264 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1235 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1235
    | (have j0 := eq1235 X0 X1
       grind)
    | exact resolve eq1235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1367 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq215 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq215
    | (have j0 := eq215 y
       grind)
    | exact resolve eq215 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1409 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1367 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ y) (σ y))
       grind)
    | exact resolve eq14 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1410 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq1409
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1409
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq1409
    | exact resolve eq1409 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1903 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq218
    | (have j0 := eq218 (M.op x y)
       grind)
    | exact resolve eq218 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1958 : (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1903 eq14
    | (have j0 := eq14 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq1903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1959 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq1958
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq1958
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq1958
    | exact resolve eq1958 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq5403 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq88 eq98
    | (have r₁ := eq98 (M.op x y) x
       have r₂ := eq88 (M.op x y)
       grind)
    | exact resolve eq98 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq5404 : y ≠ y ∨ y = (k (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq77 eq98
    | (have r₁ := eq98 y (M.op x y)
       have r₂ := eq77 y
       grind)
    | exact resolve eq98 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq5409 : y = (k (M.op x y) (M.op y y)) := by grind
  clear eq5404
  have eq5410 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5403
  have eq5414 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5409 eq1410
    | exact resolve eq1410 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq5415 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5409 eq1367
    | exact resolve eq1367 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367 eq5409
  have eq5417 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5410 eq1959
    | exact resolve eq1959 eq5410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq5418 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5410 eq1903
    | exact resolve eq1903 eq5410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq5419 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq5415
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5415
    | exact resolve eq5415 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5415
  have eq5420 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq5414
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5414
    | exact resolve eq5414 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414
  have eq5422 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5418
    | exact resolve eq5418 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5418
  have eq5423 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq5417
    | exact resolve eq5417 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5417
  have eq20395 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq5410
       have i₂ := eq1264 x (M.op sF0 sF0)
       grind)
    | exact superpose eq1264 eq5410
    | (have j1 := eq1264 x (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq5410 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq20694 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq20395
       have i₂ := eq138 sF0
       grind)
    | exact superpose eq138 eq20395
    | exact resolve eq20395 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20395
  have eq20922 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq20694
    | exact resolve eq20694 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20694
  have eq21068 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq20922
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20922
    | exact resolve eq20922 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20922
  have eq21175 : (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21068
       have i₂ := eq138 sF0
       grind)
    | exact superpose eq138 eq21068
    | exact resolve eq21068 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21068
  have eq21235 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21175
       have i₂ := eq53 (σ sF0) (σ sF0) (σ sF0)
       grind)
    | (have i₁ := eq21175
       have i₂ := eq53 x (M.op (M.op (σ sF0) (σ sF0)) (M.op (σ sF0) (σ sF0))) x
       grind)
    | exact superpose eq53 eq21175
    | exact resolve eq21175 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21175
  have eq21290 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq21235
    | exact resolve eq21235 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21235
  have eq21335 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21290
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21290
    | exact resolve eq21290 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21290
  have eq80840 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq5420 eq53
    | exact resolve eq53 eq5420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5420
  have eq80861 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5423 eq82
    | exact resolve eq82 eq5423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq80862 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq5423 eq53
    | exact resolve eq53 eq5423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5423
  have eq85478 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq80862 eq81
    | exact resolve eq81 eq80862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq80862
  have eq85500 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq85478 eq53
    | exact resolve eq53 eq85478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85478
  have eq85518 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq85500 eq80840
    | exact resolve eq80840 eq85500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85500
  have eq85538 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq85518
    | exact resolve eq85518 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85518
  have eq85542 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq85538
       have r₂ := eq27
       grind)
    | exact resolve eq85538 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85538
  have eq85606 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq85542 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ y) (σ y))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ y) (σ y))
       have r₂ := eq85542
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq85542
       grind)
    | exact resolve eq13 eq85542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85607 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq85542 eq53
    | exact resolve eq53 eq85542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85542
  have eq85620 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq85606
  have eq85630 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq85620
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq85620
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq85620
    | exact resolve eq85620 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85620
  have eq85631 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq85630
  have eq85640 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5419 eq85631
    | exact resolve eq85631 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85631
  have eq85650 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq85640 eq53
    | exact resolve eq53 eq85640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85640
  have eq86251 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq85607 eq85607
    | exact resolve eq85607 eq85607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85607
  have eq86278 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq86251
  have eq86288 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq86278 eq53
    | exact resolve eq53 eq86278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86278
  have eq86511 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq85650 eq85650
    | exact resolve eq85650 eq85650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85650
  have eq86538 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq86511
  have eq86565 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq86538 eq258
    | exact resolve eq258 eq86538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86538
  have eq86610 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38 eq86565
    | exact resolve eq86565 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86565
  have eq93497 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq86288 eq86288
    | exact resolve eq86288 eq86288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86288
  have eq93555 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq93497
  have eq93606 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq93555 eq258
    | exact resolve eq258 eq93555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93555
  have eq93668 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38 eq93606
    | exact resolve eq93606 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93606
  have eq93704 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq93668 eq86610
    | exact resolve eq86610 eq93668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86610 eq93668
  have eq93750 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq93704
  have eq94242 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq138 x
       have i₂ := eq93750
       grind)
    | exact superpose eq93750 eq138
    | exact resolve eq138 eq93750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93750
  have eq94299 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq94242
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94242
    | exact resolve eq94242 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94242
  have eq94408 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq94299 eq54
    | exact resolve eq54 eq94299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq94299
  have eq94710 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq80861 eq94408
    | exact resolve eq94408 eq80861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80861
  have eq94800 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq94710
  have eq118836 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq94800 eq94408
    | exact resolve eq94408 eq94800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94800
  have eq118875 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq118836
  have eq130545 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq118875 eq13
    | (have j0 := eq13 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq118875
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq118875
       grind)
    | exact resolve eq13 eq118875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118875
  have eq130559 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq130545
  have eq130587 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq130559
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq130559
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq130559
    | exact resolve eq130559 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130559
  have eq130588 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq130587
  have eq130597 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq5422 eq130588
    | exact resolve eq130588 eq5422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5422 eq130588
  have eq130648 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq130597 eq94408
    | exact resolve eq94408 eq130597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94408 eq130597
  have eq130746 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq130648
  have eq130830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq130746 eq80840
    | exact resolve eq80840 eq130746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130842 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq130746 eq53
    | exact resolve eq53 eq130746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130864 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq130830
  have eq130885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq130864
    | exact resolve eq130864 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130864
  have eq130892 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq130885
       have r₂ := eq27
       grind)
    | exact resolve eq130885 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130885
  have eq131332 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq130892 eq130842
    | exact resolve eq130842 eq130892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130842 eq130892
  have eq131354 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq131332
  have eq131396 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq131354 eq130746
    | exact resolve eq130746 eq131354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130746 eq131354
  have eq131453 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq131396
  have eq131469 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq131453 eq39
    | exact resolve eq39 eq131453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq131453
  have eq131556 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq131469
    | exact resolve eq131469 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131469
  have eq131564 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131556 eq38
    | exact resolve eq38 eq131556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq131556
  have eq131650 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq131564
    | exact resolve eq131564 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131564
  have eq131654 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131650 eq20
    | exact resolve eq20 eq131650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131655 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq131650 eq77
    | exact resolve eq77 eq131650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131768 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq131771 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131654
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq131654
    | exact resolve eq131654 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131654
  have eq132566 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131655 (M.op y x)
       have i₂ := eq131655 x
       grind)
    | exact superpose eq131655 eq131655
    | exact resolve eq131655 eq131655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131655
  have eq132588 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq132566
  have eq132632 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138 y
       have i₂ := eq132588
       grind)
    | exact superpose eq132588 eq138
    | exact resolve eq138 eq132588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132588
  have eq132675 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132632
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq132632
    | exact resolve eq132632 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132632
  have eq132752 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131771 eq132675
    | exact resolve eq132675 eq131771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132787 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq132675 eq78
    | exact resolve eq78 eq132675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq132675
  have eq132829 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq132752
  have eq132965 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq132829 eq258
    | exact resolve eq258 eq132829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq132829
  have eq133016 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq132965
    | exact resolve eq132965 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq132965
  have eq133112 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq133016 eq5410
    | exact resolve eq5410 eq133016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5410 eq133016
  have eq133361 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq131650 eq133112
    | exact resolve eq133112 eq131650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131650 eq133112
  have eq133413 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq133361
       have r₂ := eq131768
       grind)
    | exact resolve eq133361 eq131768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133361
  have eq133556 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq133413
       grind)
    | exact superpose eq133413 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq133413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133413
  have eq133584 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq133556
       have r₂ := eq131768
       grind)
    | exact resolve eq133556 eq131768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131768 eq133556
  have eq133607 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133584
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133584
    | exact resolve eq133584 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133584
  have eq133608 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq133607
  have eq133628 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133608
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133608
    | exact resolve eq133608 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq133608
  have eq133704 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq133628
       grind)
    | exact superpose eq133628 eq77
    | exact resolve eq77 eq133628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq133628
  have eq133799 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq133704 eq138
    | exact resolve eq138 eq133704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133704
  have eq133845 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq133799
    | exact resolve eq133799 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133799
  have eq133851 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133845
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq133845
    | exact resolve eq133845 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq133845
  have eq134164 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq133851 eq21335
    | exact resolve eq21335 eq133851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21335 eq133851
  have eq134232 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq134164
  have eq134256 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq134232
    | exact resolve eq134232 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134232
  have eq134274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq134256
    | exact resolve eq134256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134256
  have eq134276 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq134274
       have r₂ := eq27
       grind)
    | exact resolve eq134274 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134274
  have eq134318 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq134276 eq132787
    | exact resolve eq132787 eq134276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132787 eq134276
  have eq134323 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq134318
  have eq134327 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq134323
    | exact resolve eq134323 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134323
  have eq134340 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq134327 eq27
    | exact resolve eq27 eq134327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134327
  have eq134403 : x = (M.op x y) := by
    first
    | (have r₁ := eq134340
       have r₂ := eq131771
       grind)
    | exact resolve eq134340 eq131771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131771 eq134340
  have eq134406 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq134403 eq20
    | exact resolve eq20 eq134403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq134415 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq134403 eq80
    | exact resolve eq80 eq134403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq134403
  have eq151089 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq134406
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq134406
    | exact resolve eq134406 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134406
  have eq151351 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq151089 eq22
    | exact resolve eq22 eq151089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq151352 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq151089 eq26
    | exact resolve eq26 eq151089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq151089
  have eq157411 : x = (M.op x x) := by
    first
    | (have i₁ := eq134415 (M.op x x)
       have i₂ := eq134415 x
       grind)
    | exact superpose eq134415 eq134415
    | exact resolve eq134415 eq134415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134415
  have eq157717 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq138 x
       have i₂ := eq157411
       grind)
    | exact superpose eq157411 eq138
    | exact resolve eq138 eq157411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq157411
  have eq157815 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq157717
       have i₂ := eq151351
       grind)
    | exact superpose eq151351 eq157717
    | exact resolve eq157717 eq151351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151351 eq157717
  have eq158079 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq157815 eq80840
    | exact resolve eq80840 eq157815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80840
  have eq158177 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq151352 eq158079
    | exact resolve eq158079 eq151352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158079
  have eq158201 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq158177
       have r₂ := eq27
       grind)
    | exact resolve eq158177 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158177
  have eq161745 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq158201 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ y) (σ y))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ y) (σ y))
       have r₂ := eq158201
       grind)
    | exact resolve eq13 eq158201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158201
  have eq161759 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq161745
  have eq161769 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq161759
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq161759
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq161759
    | exact resolve eq161759 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq161759
  have eq161770 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by grind
  clear eq161769
  have eq161781 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5419 eq161770
    | exact resolve eq161770 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5419 eq161770
  have eq161786 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq157815 eq161781
    | exact resolve eq161781 eq157815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161781
  have eq161787 : (σ (M.op x y)) = (σ y) := by grind
  clear eq161786
  have eq165450 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq161787 eq151352
    | exact resolve eq151352 eq161787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151352 eq161787
  have eq165638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq157815 eq165450
    | exact resolve eq165450 eq157815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157815 eq165450
  have eq166209 : False := by grind
  exact eq166209

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_x_pxy_pxy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
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
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq78 eq53
    | exact resolve eq53 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 x) (M.op x x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (k (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq83 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq99 (σ X0)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq137 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq137
    | exact resolve eq137 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq137
  have eq144 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq85 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq10
    | exact resolve eq10 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq28
    | exact resolve eq28 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq218 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq31
    | exact resolve eq31 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq258 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq212 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq212
    | exact resolve eq212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq377 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X0 X2) (M.op X0 X2)) = X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 x) (M.op x x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq13
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq83 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq380 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq390 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have j0 := eq380 X0
       have j1 := eq144 X0
       grind)
    | (have r₁ := eq380 X0
       have r₂ := eq144 X0
       grind)
    | exact resolve eq380 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq380
  have eq392 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ (M.op x y) = (k (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have j0 := eq378 X0
       have j1 := eq95 X0
       grind)
    | (have r₁ := eq378 X0
       have r₂ := eq95 X0
       grind)
    | exact resolve eq378 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq378
  have eq393 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq377 X0 X1 X2
       have j1 := eq94 X0 X1 X2
       grind)
    | (have r₁ := eq377 X0 X1 X2
       have r₂ := eq94 X0 X1 X2
       grind)
    | exact resolve eq377 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq397 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq81 eq390
    | exact resolve eq390 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq399 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | exact superpose eq64 eq397
    | exact resolve eq397 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq400 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq80 eq392
    | exact resolve eq392 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq1336 : ∀ X0 X2 X3 : G, (M.op X0 X2) ≠ X0 ∨ (M.op X0 X2) = (k X0 (M.op (M.op X0 X2) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq393 (M.op x x) (M.op X0 x) X2
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq393
    | exact resolve eq393 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq1393 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq215 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq215
    | (have j0 := eq215 y
       grind)
    | exact resolve eq215 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1711 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1393 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ y) (σ y))
       grind)
    | exact resolve eq14 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1712 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq1711
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1711
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq1711
    | exact resolve eq1711 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711
  have eq1929 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq218
    | (have j0 := eq218 (M.op x y)
       grind)
    | exact resolve eq218 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq2308 : (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1929 eq14
    | (have j0 := eq14 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2309 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2308
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2308
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2308
    | exact resolve eq2308 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq3655 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1 X0
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X1 X0
       grind)
    | (have r₁ := eq94 x X1 x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3656 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3655 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3655
  have eq3661 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq80 eq3656
    | exact resolve eq3656 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3663 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq81 eq3656
    | exact resolve eq3656 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3664 : y = (k (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq3656 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3656
    | (have j0 := eq3656 y x
       grind)
    | exact resolve eq3656 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3656
  have eq3684 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3664 eq1712
    | exact resolve eq1712 eq3664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712
  have eq3685 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3664 eq1393
    | exact resolve eq1393 eq3664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393 eq3664
  have eq3687 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3661 eq2309
    | exact resolve eq2309 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309
  have eq3688 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3661 eq1929
    | exact resolve eq1929 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929
  have eq3692 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq3685
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3685
    | exact resolve eq3685 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685
  have eq3693 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq3684
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3684
    | exact resolve eq3684 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3684
  have eq3695 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq3688
    | exact resolve eq3688 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3688
  have eq3696 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq3687
    | exact resolve eq3687 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3687
  have eq81746 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq3693 eq53
    | exact resolve eq53 eq3693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693
  have eq81763 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3696 eq82
    | exact resolve eq82 eq3696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq81764 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3696 eq53
    | exact resolve eq53 eq3696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696
  have eq86925 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq81764 eq81
    | exact resolve eq81 eq81764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq81764
  have eq86949 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq86925 eq53
    | exact resolve eq53 eq86925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86925
  have eq86978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq86949 eq81746
    | exact resolve eq81746 eq86949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86949
  have eq86998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq86978
    | exact resolve eq86978 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86978
  have eq87001 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq86998
       have r₂ := eq27
       grind)
    | exact resolve eq86998 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86998
  have eq87012 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq87001 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ y) (σ y))
       have r₂ := eq87001
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq87001
       grind)
    | exact resolve eq13 eq87001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87001
  have eq87028 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq87012
  have eq87037 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq87028
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq87028
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq87028
    | exact resolve eq87028 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87028
  have eq87038 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq87037
  have eq87047 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3692 eq87038
    | exact resolve eq87038 eq3692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87038
  have eq87048 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq87047
  have eq87058 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq87048 eq54
    | exact resolve eq54 eq87048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq87063 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq87048 eq1336
    | (have r₁ := eq1336 (σ x) (M.op (σ x) (σ y)) x
       have r₂ := eq87048
       grind)
    | exact resolve eq1336 eq87048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336 eq87048
  have eq87069 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq87063 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87063
  have eq87449 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq81763 eq87058
    | exact resolve eq87058 eq81763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81763 eq87058
  have eq87485 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq87449
  have eq120319 : (σ x) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq87485 eq87069
    | exact resolve eq87069 eq87485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87069 eq87485
  have eq120360 : (σ x) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq120319
  have eq120374 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3695 eq120360
    | exact resolve eq120360 eq3695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3695 eq120360
  have eq120375 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq120374
  have eq120396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq120375 eq81746
    | exact resolve eq81746 eq120375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120375
  have eq120418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq120396
  have eq120438 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq120418
    | exact resolve eq120418 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120418
  have eq120451 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq120438
       have r₂ := eq27
       grind)
    | exact resolve eq120438 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120438
  have eq120583 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq120451 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ y) (σ y))
       have r₂ := eq120451
       grind)
    | exact resolve eq13 eq120451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120451
  have eq120599 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq120583
  have eq120612 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq120599
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq120599
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq120599
    | exact resolve eq120599 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120599
  have eq120613 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq120612
  have eq120622 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3692 eq120613
    | exact resolve eq120613 eq3692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120613
  have eq120623 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq120622
  have eq120631 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq120623 eq39
    | exact resolve eq39 eq120623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq120623
  have eq120700 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq120631
    | exact resolve eq120631 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120631
  have eq120708 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120700 eq38
    | exact resolve eq38 eq120700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120700
  have eq120777 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq120708
    | exact resolve eq120708 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120708
  have eq120781 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120777 eq20
    | exact resolve eq20 eq120777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120782 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq120777 eq77
    | exact resolve eq77 eq120777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120903 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq120907 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120781
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq120781
    | exact resolve eq120781 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120781
  have eq121488 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120782 (M.op y x)
       have i₂ := eq120782 x
       grind)
    | exact superpose eq120782 eq120782
    | exact resolve eq120782 eq120782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120782
  have eq121514 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq121488
  have eq121548 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138 y
       have i₂ := eq121514
       grind)
    | exact superpose eq121514 eq138
    | exact resolve eq138 eq121514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121514
  have eq121594 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121548
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121548
    | exact resolve eq121548 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq121548
  have eq121667 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120907 eq121594
    | exact resolve eq121594 eq120907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120907 eq121594
  have eq121732 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq121667
  have eq121973 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121732 eq258
    | exact resolve eq258 eq121732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq121732
  have eq122022 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq121973
    | exact resolve eq121973 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121973
  have eq122103 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122022 eq3661
    | exact resolve eq3661 eq122022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122022
  have eq122173 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq120777 eq122103
    | exact resolve eq122103 eq120777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120777 eq122103
  have eq122248 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122173
       have r₂ := eq120903
       grind)
    | exact resolve eq122173 eq120903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122173
  have eq122402 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq122248
       grind)
    | exact superpose eq122248 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq122248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122248
  have eq122430 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122402
       have r₂ := eq120903
       grind)
    | exact resolve eq122402 eq120903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120903 eq122402
  have eq122453 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122430
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122430
    | exact resolve eq122430 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122430
  have eq122454 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq122453
  have eq122474 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122454
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122454
    | exact resolve eq122454 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq122454
  have eq122550 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq122474
       grind)
    | exact superpose eq122474 eq77
    | exact resolve eq77 eq122474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq122474
  have eq122618 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122550 eq3661
    | exact resolve eq3661 eq122550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661 eq122550
  have eq122677 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq122618
       have r₂ := eq400
       grind)
    | exact resolve eq122618 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq122618
  have eq122685 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq64
       have i₂ := eq122677
       grind)
    | exact superpose eq122677 eq64
    | exact resolve eq64 eq122677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq122688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq399
       have i₂ := eq122677
       grind)
    | exact superpose eq122677 eq399
    | exact resolve eq399 eq122677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq122677
  have eq122958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq122688
    | exact resolve eq122688 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122688
  have eq122961 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq122685
    | exact resolve eq122685 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq122685
  have eq122962 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq122958
       have r₂ := eq27
       grind)
    | exact resolve eq122958 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122958
  have eq122973 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq122961 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq122961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122993 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq122973
    | exact resolve eq122973 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122973
  have eq123005 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq122993
       have r₂ := eq122962
       grind)
    | exact resolve eq122993 eq122962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122962 eq122993
  have eq123014 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq123005
    | exact resolve eq123005 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123005
  have eq130851 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq123014 eq78
    | exact resolve eq78 eq123014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq123014
  have eq131002 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq130851 eq3663
    | exact resolve eq3663 eq130851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663 eq130851
  have eq131056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq122961 eq131002
    | exact resolve eq131002 eq122961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122961 eq131002
  have eq131057 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq131056
       have r₂ := eq27
       grind)
    | exact resolve eq131056 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131056
  have eq131058 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq131057 eq22
    | exact resolve eq22 eq131057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq131059 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq131057 eq26
    | exact resolve eq26 eq131057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq131063 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq131057 eq38
    | exact resolve eq38 eq131057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq131057
  have eq137402 : x = (M.op x y) := by
    first
    | exact superpose eq37 eq131063
    | exact resolve eq131063 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq131063
  have eq138163 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq137402 eq80
    | exact resolve eq80 eq137402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq137402
  have eq149075 : x = (M.op x x) := by
    first
    | (have i₁ := eq138163 (M.op x x)
       have i₂ := eq138163 x
       grind)
    | exact superpose eq138163 eq138163
    | exact resolve eq138163 eq138163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138163
  have eq149389 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq138 x
       have i₂ := eq149075
       grind)
    | exact superpose eq149075 eq138
    | exact resolve eq138 eq149075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq149075
  have eq149485 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq149389
       have i₂ := eq131058
       grind)
    | exact superpose eq131058 eq149389
    | exact resolve eq149389 eq131058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131058 eq149389
  have eq149708 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq149485 eq81746
    | exact resolve eq81746 eq149485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81746
  have eq149806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq131059 eq149708
    | exact resolve eq149708 eq131059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149708
  have eq149824 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq149806
       have r₂ := eq27
       grind)
    | exact resolve eq149806 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149806
  have eq154587 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq149824 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ y) (σ y))
       have r₂ := eq149824
       grind)
    | exact resolve eq13 eq149824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149824
  have eq154603 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq154587
  have eq154610 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq154603
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq154603
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq154603
    | exact resolve eq154603 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq154603
  have eq154611 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by grind
  clear eq154610
  have eq154622 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3692 eq154611
    | exact resolve eq154611 eq3692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3692 eq154611
  have eq154623 : (σ (M.op x y)) = (σ y) := by grind
  clear eq154622
  have eq157780 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq154623 eq131059
    | exact resolve eq131059 eq154623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131059 eq154623
  have eq158305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq149485 eq157780
    | exact resolve eq157780 eq149485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149485 eq157780
  have eq158803 : False := by grind
  exact eq158803

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if m(Y,Y) = X then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyy_x_pyy_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq24 X2 X0 x
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq90 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq24
    | exact resolve eq24 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq105 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq108 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq105
    | (have j0 := eq105 X0 X1
       grind)
    | exact resolve eq105 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq235 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 (M.op X1 (M.op X0 X0)) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op x x)) x
       have r₂ := eq30 x X1 x
       grind)
    | exact resolve eq12 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq235 (M.op x x) X1
       have i₂ := eq24 x x x
       grind)
    | exact superpose eq24 eq235
    | exact resolve eq235 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq355 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X0)) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (σ (M.op X1 X0)) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X1 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq108 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq280 X0 X1
       grind)
    | exact superpose eq280 eq108
    | (have j0 := eq108 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq108 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq280
  have eq359 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X1 X0)) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X1 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 X1
       have i₂ := eq24 X0 X0 X0
       grind)
    | (have i₁ := eq355 X0 X1
       have i₂ := eq24 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq24 eq355
    | (have j0 := eq355 X0 X1
       grind)
    | exact resolve eq355 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq360 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X0)) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X1 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq359 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq366 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X0)) ∨ (σ X0) = (M.op (σ (M.op X1 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 X1
       have i₂ := eq24 X0 X0 X0
       grind)
    | (have i₁ := eq360 X0 X1
       have i₂ := eq24 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq24 eq360
    | (have j0 := eq360 X0 X1
       grind)
    | exact resolve eq360 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq10581 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X0) ∨ (σ X0) = (M.op (σ (M.op X1 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X0)
       have i₂ := eq366 X0 X1
       grind)
    | exact superpose eq366 eq10
    | (have j1 := eq366 X0 X1
       grind)
    | exact resolve eq10 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq10638 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (σ (M.op X0 X0))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10581 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10581
    | (have j0 := eq10581 X0 X1
       grind)
    | exact resolve eq10581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10581
  have eq11205 : ∀ X0 X1 X2 : G, (σ (M.op X2 X0)) = (M.op (M.op X1 (σ (M.op X2 X0))) (σ X0)) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (σ (M.op X2 X0)) (σ (M.op X0 X0))
       have i₂ := eq10638 X0 X2
       grind)
    | exact superpose eq10638 eq24
    | (have j1 := eq10638 X0 X2
       grind)
    | exact resolve eq24 eq10638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13059 : ∀ X0 X2 X3 : G, (σ X0) = (M.op (M.op X3 (σ X0)) (σ (M.op X0 X2))) ∨ (M.op X0 X2) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq11205 (M.op x x) x (M.op X0 x)
       have i₂ := eq24 X0 x x
       grind)
    | exact superpose eq24 eq11205
    | exact resolve eq11205 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13657 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11205 X1 (M.op x (σ X0)) X0
       have i₂ := eq13059 X0 X1 x
       grind)
    | exact superpose eq13059 eq11205
    | (have j0 := eq11205 X1 X1 X0
       have j1 := eq13059 X0 X1 x
       grind)
    | exact resolve eq11205 eq13059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11205 eq13059
  have eq34340 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13657 x y
       grind)
    | exact superpose eq13657 eq16
    | (have j1 := eq13657 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq13657 x y
       grind)
    | exact resolve eq16 eq13657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13657
  have eq34669 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq34340
  have eq34872 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq24 X0 x y
       have i₂ := eq34669
       grind)
    | exact superpose eq34669 eq24
    | exact resolve eq24 eq34669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34873 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq24 x y X0
       have i₂ := eq34669
       grind)
    | exact superpose eq34669 eq24
    | exact resolve eq24 eq34669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34669
  have eq35248 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op (M.op X1 x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq30 y X1 x
       have i₂ := eq34872 X0
       grind)
    | exact superpose eq34872 eq30
    | (have j1 := eq34872 X0
       grind)
    | exact resolve eq30 eq34872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq34872
  have eq35279 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op y (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 x y
       have i₂ := eq34873 X1
       grind)
    | exact superpose eq34873 eq24
    | (have j1 := eq34873 X1
       grind)
    | exact resolve eq24 eq34873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34873
  have eq37178 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have j0 := eq35248 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35248
  have eq37179 : ∀ X0 : G, x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have j0 := eq37178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37178
  have eq37190 : ∀ X1 : G, y = (M.op x (M.op y X1)) := by
    intro X1
    first
    | (have i₁ := eq24 (M.op x x) y X1
       have i₂ := eq37179 x
       grind)
    | exact superpose eq37179 eq24
    | exact resolve eq24 eq37179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq37213 : x = y ∨ (σ y) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq10638 y (M.op x x)
       have i₂ := eq37179 x
       grind)
    | exact superpose eq37179 eq10638
    | exact resolve eq10638 eq37179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10638
  have eq37775 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37213
       grind)
    | exact superpose eq37213 eq16
    | exact resolve eq16 eq37213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37213
  have eq37793 : (σ y) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have r₁ := eq37775
       have r₂ := eq63 x
       grind)
    | exact resolve eq37775 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq37775
  have eq37803 : (σ x) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq90 x (σ (M.op y y))
       have i₂ := eq37793
       grind)
    | exact superpose eq37793 eq90
    | exact resolve eq90 eq37793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq41580 : ∀ X1 X2 : G, y = (M.op y (M.op y X1)) ∨ x = (M.op x x) ∨ y = (M.op y (M.op y X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq35279 (M.op x x) X1
       have i₂ := eq35279 x X2
       grind)
    | exact superpose eq35279 eq35279
    | (have j0 := eq35279 x X1
       have j1 := eq35279 x X1
       grind)
    | exact resolve eq35279 eq35279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35279
  have eq59590 : ∀ X0 : G, y ≠ y ∨ x = (M.op x x) ∨ y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have j0 := eq41580 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41580
  have eq59591 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq59590 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59590
  have eq59604 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq59591 (M.op y x)
       have i₂ := eq59591 x
       grind)
    | exact superpose eq59591 eq59591
    | exact resolve eq59591 eq59591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59591
  have eq59663 : x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq59604
  have eq60721 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq37803
       have i₂ := eq59663
       grind)
    | exact superpose eq59663 eq37803
    | exact resolve eq37803 eq59663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37803
  have eq60733 : x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq37179 x
       have i₂ := eq59663
       grind)
    | exact superpose eq59663 eq37179
    | exact resolve eq37179 eq59663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37179 eq59663
  have eq63752 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60721
       grind)
    | exact superpose eq60721 eq16
    | exact resolve eq16 eq60721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60721
  have eq63862 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq63752
       have i₂ := eq60733
       grind)
    | exact superpose eq60733 eq63752
    | exact resolve eq63752 eq60733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60733 eq63752
  have eq63864 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by grind
  clear eq63862
  have eq63865 : y = (M.op y y) := by grind
  clear eq63864
  have eq63896 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37793
       have i₂ := eq63865
       grind)
    | exact superpose eq63865 eq37793
    | exact resolve eq37793 eq63865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37793
  have eq63910 : y = (M.op x y) := by
    first
    | (have i₁ := eq37190 y
       have i₂ := eq63865
       grind)
    | exact superpose eq63865 eq37190
    | exact resolve eq37190 eq63865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37190 eq63865
  have eq66161 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63896
       grind)
    | exact superpose eq63896 eq16
    | exact resolve eq16 eq63896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63896
  have eq66223 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq66161
       have i₂ := eq63910
       grind)
    | exact superpose eq63910 eq66161
    | exact resolve eq66161 eq63910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63910 eq66161
  have eq66224 : False := by grind
  exact eq66224

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then Y else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_y_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
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
  have eq40 : y = (τ (σ y)) := by
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
  have eq54 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq54 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y X0
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 X0 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 x) (M.op x x)
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq12
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq136 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq136
    | exact resolve eq136 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq211 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq10
    | exact resolve eq10 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 (M.op X0 X0)
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq29
    | exact resolve eq29 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq217 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 (M.op X0 X0)
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq32
    | exact resolve eq32 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq257 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq211 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq211
    | exact resolve eq211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq1622 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq214 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq214
    | (have j0 := eq214 y
       grind)
    | exact resolve eq214 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1664 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1622 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ y) (σ y))
       grind)
    | exact resolve eq14 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq1665 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1664
       have i₂ := eq54 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1664
       have i₂ := eq54 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq54 eq1664
    | exact resolve eq1664 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664
  have eq1873 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq217
    | (have j0 := eq217 (M.op x y)
       grind)
    | exact resolve eq217 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq2249 : (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1873 eq14
    | (have j0 := eq14 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq2250 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2249
       have i₂ := eq54 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2249
       have i₂ := eq54 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq54 eq2249
    | exact resolve eq2249 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249
  have eq3250 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1 X0
       have i₂ := eq54 X0 X0 X0
       grind)
    | exact superpose eq54 eq95
    | (have j0 := eq95 X0 X1 X0
       grind)
    | (have r₁ := eq95 x X1 x
       have r₂ := eq54 x x x
       grind)
    | exact resolve eq95 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3251 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3250
  have eq3256 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq81 eq3251
    | exact resolve eq3251 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3259 : y = (k (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq3251 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3251
    | (have j0 := eq3251 y x
       grind)
    | exact resolve eq3251 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3277 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3259 eq1665
    | exact resolve eq1665 eq3259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665 eq3259
  have eq3280 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3256 eq2250
    | exact resolve eq2250 eq3256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250
  have eq3284 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3277
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3277
    | exact resolve eq3277 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3277
  have eq3287 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq3280
    | exact resolve eq3280 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280
  have eq11582 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq3284 eq54
    | exact resolve eq54 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284
  have eq11595 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3287 eq54
    | exact resolve eq54 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq12847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11595 eq11582
    | exact resolve eq11582 eq11595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11595
  have eq12862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq12847
    | exact resolve eq12847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12847
  have eq12864 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq12862
       have r₂ := eq28
       grind)
    | exact resolve eq12862 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12862
  have eq12896 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12864 eq3251
    | exact resolve eq3251 eq12864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12864
  have eq12902 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq12896
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq12896
    | exact resolve eq12896 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12896
  have eq12959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12902 eq3287
    | exact resolve eq3287 eq12902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12986 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq12902
  have eq12989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq12959
  have eq13001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq12989
       have r₂ := eq12986
       grind)
    | exact resolve eq12989 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12986 eq12989
  have eq13011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq13001
    | exact resolve eq13001 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13001
  have eq13012 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq13011
       have r₂ := eq28
       grind)
    | exact resolve eq13011 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13011
  have eq13668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13012 eq11582
    | exact resolve eq11582 eq13012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13688 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13012 eq3251
    | exact resolve eq3251 eq13012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13668
  have eq13696 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13688
       have i₂ := eq100 sF2
       grind)
    | exact superpose eq100 eq13688
    | exact resolve eq13688 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13688
  have eq13704 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq13692
    | exact resolve eq13692 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13692
  have eq13716 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq13704
       have r₂ := eq28
       grind)
    | exact resolve eq13704 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13704
  have eq13842 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13716 eq3251
    | exact resolve eq3251 eq13716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13716
  have eq13848 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13842
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq13842
    | exact resolve eq13842 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13842
  have eq13954 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13848 eq13012
    | exact resolve eq13012 eq13848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13012 eq13848
  have eq13980 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13954
  have eq14003 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13980 eq27
    | exact resolve eq27 eq13980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14007 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13980 eq40
    | exact resolve eq40 eq13980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13980
  have eq14067 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq39 eq14007
    | exact resolve eq14007 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14007
  have eq14076 : y = (τ (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14067 eq40
    | exact resolve eq40 eq14067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14067
  have eq14124 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq14076
    | exact resolve eq14076 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14076
  have eq14132 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq14124 eq39
    | exact resolve eq39 eq14124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14124
  have eq14178 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq14132
    | exact resolve eq14132 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14132
  have eq15553 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14003 eq13696
    | exact resolve eq13696 eq14003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13696 eq14003
  have eq15580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq15553
  have eq15589 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq15580
       have r₂ := eq28
       grind)
    | exact resolve eq15580 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15580
  have eq15596 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15589 eq40
    | exact resolve eq40 eq15589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15589
  have eq15644 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq15596
    | exact resolve eq15596 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15596
  have eq15652 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15644 eq39
    | exact resolve eq39 eq15644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15644
  have eq15698 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq15652
    | exact resolve eq15652 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15652
  have eq15702 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15698 eq21
    | exact resolve eq21 eq15698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15703 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15698 eq78
    | exact resolve eq78 eq15698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15730 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq15698
  have eq15731 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15702
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15702
    | exact resolve eq15702 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15702
  have eq16334 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15703 (M.op y x)
       have i₂ := eq15703 x
       grind)
    | exact superpose eq15703 eq15703
    | exact resolve eq15703 eq15703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15703
  have eq16349 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq16334
  have eq16375 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq137 y
       have i₂ := eq16349
       grind)
    | exact superpose eq16349 eq137
    | exact resolve eq137 eq16349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16349
  have eq16400 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16375
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16375
    | exact resolve eq16375 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16375
  have eq16435 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15731 eq16400
    | exact resolve eq16400 eq15731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16400
  have eq16492 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq16435
  have eq16591 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16492 eq257
    | exact resolve eq257 eq16492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq16492
  have eq16622 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq16591
    | exact resolve eq16591 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16591
  have eq16692 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16622 eq3256
    | exact resolve eq3256 eq16622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256 eq16622
  have eq18074 : y = (k x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14178 eq16692
    | exact resolve eq16692 eq14178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14178 eq16692
  have eq18093 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18074
  have eq18104 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18093
       have r₂ := eq15730
       grind)
    | exact resolve eq18093 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18093
  have eq18167 : x = y ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18104
       grind)
    | exact superpose eq18104 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18104
  have eq18175 : x = y ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq18167
  have eq18182 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18175
       have r₂ := eq15730
       grind)
    | exact resolve eq18175 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15730 eq18175
  have eq18198 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18182
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18182
    | exact resolve eq18182 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq18182
  have eq18234 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq18198
       grind)
    | exact superpose eq18198 eq78
    | exact resolve eq78 eq18198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq18198
  have eq18284 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18234 eq137
    | exact resolve eq137 eq18234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18234
  have eq18311 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq18284
    | exact resolve eq18284 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18284
  have eq18313 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18311
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18311
    | exact resolve eq18311 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18311
  have eq18476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18313 eq3287
    | exact resolve eq3287 eq18313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287 eq18313
  have eq18523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18476
    | exact resolve eq18476 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18476
  have eq18533 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18523
       have r₂ := eq28
       grind)
    | exact resolve eq18523 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18523
  have eq20551 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18533 eq15731
    | exact resolve eq15731 eq18533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15731 eq18533
  have eq20560 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq20551
  have eq20578 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20560 eq39
    | exact resolve eq39 eq20560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq20560
  have eq20626 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq20578
    | exact resolve eq20578 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq20578
  have eq20627 : x = (M.op x y) := by grind
  clear eq20626
  have eq20632 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20627 eq21
    | exact resolve eq21 eq20627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq20641 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq20627 eq81
    | exact resolve eq81 eq20627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq20627
  have eq22542 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq20632
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20632
    | exact resolve eq20632 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20632
  have eq22658 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq22542 eq23
    | exact resolve eq23 eq22542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq22659 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq22542 eq27
    | exact resolve eq27 eq22542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22542
  have eq24323 : x = (M.op x x) := by
    first
    | (have i₁ := eq20641 (M.op x x)
       have i₂ := eq20641 x
       grind)
    | exact superpose eq20641 eq20641
    | exact resolve eq20641 eq20641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20641
  have eq24762 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq137 x
       have i₂ := eq24323
       grind)
    | exact superpose eq24323 eq137
    | exact resolve eq137 eq24323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq24323
  have eq24800 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq24762
       have i₂ := eq22658
       grind)
    | exact superpose eq22658 eq24762
    | exact resolve eq24762 eq22658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22658 eq24762
  have eq24959 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq24800 eq11582
    | exact resolve eq11582 eq24800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11582
  have eq25089 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq22659 eq24959
    | exact resolve eq24959 eq22659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24959
  have eq25120 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq25089
       have r₂ := eq28
       grind)
    | exact resolve eq25089 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25089
  have eq25942 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25120 eq3251
    | exact resolve eq3251 eq25120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3251 eq25120
  have eq25948 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25942
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq25942
    | exact resolve eq25942 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq25942
  have eq25964 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24800 eq25948
    | exact resolve eq25948 eq24800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25948
  have eq25965 : (σ (M.op x y)) = (σ y) := by grind
  clear eq25964
  have eq26786 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq25965 eq22659
    | exact resolve eq22659 eq25965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22659 eq25965
  have eq26820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24800 eq26786
    | exact resolve eq26786 eq24800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24800 eq26786
  have eq27150 : False := by grind
  exact eq27150

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyy_pxy_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
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
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq80 eq53
    | exact resolve eq53 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq77 eq12
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq138 : ∀ X0 : G, x ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq88 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq200 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq158 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq158
    | exact resolve eq158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq307 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op x x)
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq308 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq308 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq308 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq317 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq200 X0 X0
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq200
    | exact resolve eq200 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq309 (σ X0)
       grind)
    | exact superpose eq309 eq15
    | exact resolve eq15 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq319 X0
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq319
    | exact resolve eq319 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq322 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq317 X0
       have i₂ := eq309 (τ X0)
       grind)
    | exact superpose eq309 eq317
    | exact resolve eq317 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq317
  have eq333 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq320 X0
       grind)
    | exact superpose eq320 eq28
    | exact resolve eq28 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq336 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 (M.op X0 X0)
       have i₂ := eq320 X0
       grind)
    | exact superpose eq320 eq31
    | exact resolve eq31 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq846 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq116 X0 X1
       grind)
    | exact superpose eq116 eq10
    | (have j1 := eq116 X0 X1
       grind)
    | exact resolve eq10 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq870 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq846 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq846
    | (have j0 := eq846 X0 X1
       grind)
    | exact resolve eq846 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq1369 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq333 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq333
    | (have j0 := eq333 y
       grind)
    | exact resolve eq333 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq1411 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1369 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ y) (σ y))
       grind)
    | exact resolve eq14 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1412 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq1411
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1411
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq1411
    | exact resolve eq1411 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq1905 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq336
    | (have j0 := eq336 (M.op x y)
       grind)
    | exact resolve eq336 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq1960 : (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1905 eq14
    | (have j0 := eq14 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq1905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1961 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq1960
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq1960
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq1960
    | exact resolve eq1960 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq8569 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq88 eq307
    | (have j0 := eq307 (M.op x y) x
       grind)
    | (have r₁ := eq307 (M.op x y) x
       have r₂ := eq88 (M.op x y)
       grind)
    | exact resolve eq307 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq8570 : y ≠ y ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq77 eq307
    | (have j0 := eq307 y (M.op x y)
       grind)
    | (have r₁ := eq307 y (M.op x y)
       have r₂ := eq77 y
       grind)
    | exact resolve eq307 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq8575 : y = (M.op x y) ∨ y = (k (M.op x y) (M.op y y)) := by grind
  clear eq8570
  have eq8576 : x = (M.op x y) ∨ (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by grind
  clear eq8569
  have eq8581 : y = (k (M.op x y) (M.op y y)) := by
    first
    | (have j1 := eq99 y
       grind)
    | (have r₁ := eq8575
       have r₂ := eq99 x
       grind)
    | exact resolve eq8575 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq8575
  have eq8582 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have j1 := eq138 (M.op x y)
       grind)
    | (have r₁ := eq8576
       have r₂ := eq138 x
       grind)
    | exact resolve eq8576 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq8576
  have eq8588 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq8581 eq1412
    | exact resolve eq1412 eq8581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq8589 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq8581 eq1369
    | exact resolve eq1369 eq8581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq8591 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq8582 eq1961
    | exact resolve eq1961 eq8582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq8592 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq8582 eq1905
    | exact resolve eq1905 eq8582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq8594 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq8589
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8589
    | exact resolve eq8589 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8589
  have eq8595 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq8588
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8588
    | exact resolve eq8588 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8588
  have eq8597 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq8592
    | exact resolve eq8592 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8592
  have eq8598 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq8591
    | exact resolve eq8591 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8591
  have eq18505 : y = (M.op x y) ∨ (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ (M.op x y)) (σ (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq8581
       have i₂ := eq870 sF0 (M.op y y)
       grind)
    | exact superpose eq870 eq8581
    | (have j1 := eq870 (M.op x y) (M.op y y)
       grind)
    | exact resolve eq8581 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq8581
  have eq18774 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq18505
       have i₂ := eq320 y
       grind)
    | exact superpose eq320 eq18505
    | exact resolve eq18505 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18505
  have eq18994 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq18774
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18774
    | exact resolve eq18774 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18774
  have eq19134 : (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | exact superpose eq20 eq18994
    | exact resolve eq18994 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18994
  have eq19231 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq19134
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq19134
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq19134
    | exact resolve eq19134 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq19134
  have eq19281 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19231
       have i₂ := eq320 y
       grind)
    | exact superpose eq320 eq19231
    | exact resolve eq19231 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19231
  have eq19314 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19281
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19281
    | exact resolve eq19281 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19281
  have eq19341 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq19314
    | exact resolve eq19314 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19314
  have eq79197 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8598 eq12
    | (have r₁ := eq12 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq8598
       grind)
    | exact resolve eq12 eq8598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8598
  have eq79208 : (σ x) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq79197
  have eq79212 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8597 eq79208
    | exact resolve eq79208 eq8597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8597 eq79208
  have eq79213 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq79212
  have eq79230 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq79213 eq54
    | exact resolve eq54 eq79213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79213
  have eq79387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19341 eq79230
    | exact resolve eq79230 eq19341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19341
  have eq79414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq79387
    | exact resolve eq79387 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79387
  have eq79417 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq79414
       have r₂ := eq27
       grind)
    | exact resolve eq79414 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79414
  have eq79428 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79417 eq12
    | (have r₁ := eq12 (σ (M.op x y)) (M.op (σ y) (σ y))
       have r₂ := eq79417
       grind)
    | exact resolve eq12 eq79417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79417
  have eq79441 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq79428
  have eq79449 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8594 eq79441
    | exact resolve eq79441 eq8594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79441
  have eq79464 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79449 eq39
    | exact resolve eq39 eq79449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq79449
  have eq79530 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq79464
    | exact resolve eq79464 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79464
  have eq79531 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq79530
  have eq79539 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79531 eq38
    | exact resolve eq38 eq79531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79531
  have eq79600 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq79539
    | exact resolve eq79539 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79539
  have eq79604 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79600 eq20
    | exact resolve eq20 eq79600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79605 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq79600 eq77
    | exact resolve eq77 eq79600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79673 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq79675 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79604
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq79604
    | exact resolve eq79604 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79604
  have eq79897 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79605 (M.op y x)
       have i₂ := eq79605 x
       grind)
    | exact superpose eq79605 eq79605
    | exact resolve eq79605 eq79605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79605
  have eq79916 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq79897
  have eq80105 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq320 y
       have i₂ := eq79916
       grind)
    | exact superpose eq79916 eq320
    | exact resolve eq320 eq79916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79916
  have eq80144 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80105
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq80105
    | exact resolve eq80105 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80105
  have eq80205 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79675 eq80144
    | exact resolve eq80144 eq79675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79675 eq80144
  have eq80256 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq80205
  have eq80361 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80256 eq322
    | exact resolve eq322 eq80256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq80256
  have eq80403 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq80361
    | exact resolve eq80361 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80361
  have eq80478 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80403 eq8582
    | exact resolve eq8582 eq80403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8582 eq80403
  have eq80535 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq79600 eq80478
    | exact resolve eq80478 eq79600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79600 eq80478
  have eq80577 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq80535
       have r₂ := eq79673
       grind)
    | exact resolve eq80535 eq79673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80535
  have eq80829 : x = y ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq80577
       grind)
    | exact superpose eq80577 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq80577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80577
  have eq80857 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq80829
       have r₂ := eq79673
       grind)
    | exact resolve eq80829 eq79673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79673 eq80829
  have eq80880 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80857
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80857
    | exact resolve eq80857 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80857
  have eq80899 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80880
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80880
    | exact resolve eq80880 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq80880
  have eq80900 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq80899
  have eq80975 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq80900
       grind)
    | exact superpose eq80900 eq77
    | exact resolve eq77 eq80900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq80900
  have eq81046 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80975 eq320
    | exact resolve eq320 eq80975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80975
  have eq81086 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq81046
    | exact resolve eq81046 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81046
  have eq81095 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81086
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq81086
    | exact resolve eq81086 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq81086
  have eq89225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81095 eq79230
    | exact resolve eq79230 eq81095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79230 eq81095
  have eq89275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq89225
    | exact resolve eq89225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89225
  have eq89291 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq89275
       have r₂ := eq27
       grind)
    | exact resolve eq89275 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89275
  have eq89298 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq89291 eq38
    | exact resolve eq38 eq89291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq89291
  have eq89358 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq89298
    | exact resolve eq89298 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq89298
  have eq89359 : x = (M.op x y) := by grind
  clear eq89358
  have eq89364 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq89359 eq20
    | exact resolve eq20 eq89359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq89373 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq89359 eq80
    | exact resolve eq80 eq89359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq89359
  have eq104536 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq89364
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq89364
    | exact resolve eq89364 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89364
  have eq104867 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq104536 eq22
    | exact resolve eq22 eq104536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq104868 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq104536 eq26
    | exact resolve eq26 eq104536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq104536
  have eq110215 : x = (M.op x x) := by
    first
    | (have i₁ := eq89373 (M.op x x)
       have i₂ := eq89373 x
       grind)
    | exact superpose eq89373 eq89373
    | exact resolve eq89373 eq89373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89373
  have eq110519 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq320 x
       have i₂ := eq110215
       grind)
    | exact superpose eq110215 eq320
    | exact resolve eq320 eq110215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq110215
  have eq110611 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq110519
       have i₂ := eq104867
       grind)
    | exact superpose eq104867 eq110519
    | exact resolve eq110519 eq104867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104867 eq110519
  have eq110876 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq110611 eq54
    | exact resolve eq54 eq110611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq112199 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq8595 eq110876
    | exact resolve eq110876 eq8595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8595 eq110876
  have eq112224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq104868 eq112199
    | exact resolve eq112199 eq104868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112199
  have eq112226 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq112224
       have r₂ := eq27
       grind)
    | exact resolve eq112224 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112224
  have eq114532 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq112226 eq12
    | (have r₁ := eq12 (σ (M.op x y)) (M.op (σ y) (σ y))
       have r₂ := eq112226
       grind)
    | exact resolve eq12 eq112226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112226
  have eq114545 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq114532
  have eq114551 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8594 eq114545
    | exact resolve eq114545 eq8594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8594 eq114545
  have eq114552 : (σ (M.op x y)) = (σ y) := by grind
  clear eq114551
  have eq117839 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq114552 eq104868
    | exact resolve eq104868 eq114552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104868 eq114552
  have eq117901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq110611 eq117839
    | exact resolve eq117839 eq110611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110611 eq117839
  have eq118175 : False := by grind
  exact eq118175

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyy_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq353 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq353 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq353 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq365 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq354 (σ X0)
       grind)
    | exact superpose eq354 eq15
    | exact resolve eq15 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq354 (τ X0)
       grind)
    | exact superpose eq354 eq31
    | exact resolve eq31 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq378 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq371
    | exact resolve eq371 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq384 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365 X0
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq365
    | exact resolve eq365 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq365
  have eq677 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 X1
       have i₂ := eq384 X1
       grind)
    | exact superpose eq384 eq677
    | (have j0 := eq677 X0 X1
       grind)
    | exact resolve eq677 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq716 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq702
    | (have j0 := eq702 X0 X1
       grind)
    | exact resolve eq702 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq2909 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq716
    | (have j0 := eq716 (τ X0) X1
       grind)
    | exact resolve eq716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq2976 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2909 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2909
    | (have j0 := eq2909 X0 X1
       grind)
    | exact resolve eq2909 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909
  have eq2998 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2976 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq2976 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq2976 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq3001 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2998 X0 X1
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq2998
    | (have j0 := eq2998 X0 X1
       grind)
    | exact resolve eq2998 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2998
  have eq3003 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3001 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3001
    | (have j0 := eq3001 X0 X1
       grind)
    | exact resolve eq3001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001
  have eq3005 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3003 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3003
    | (have j0 := eq3003 X1 (τ X0)
       grind)
    | exact resolve eq3003 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3029 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3003 (σ X1) X0
       grind)
    | exact superpose eq3003 eq15
    | (have j1 := eq3003 (σ X1) X0
       grind)
    | exact resolve eq15 eq3003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq3074 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3029 X0 X1
       have i₂ := eq384 X1
       grind)
    | exact superpose eq384 eq3029
    | (have j0 := eq3029 X0 X1
       grind)
    | exact resolve eq3029 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3029
  have eq3091 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3005 X0 X1
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq3005
    | (have j0 := eq3005 X0 X1
       grind)
    | exact resolve eq3005 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005
  have eq3098 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3091 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3091
    | (have j0 := eq3091 X0 X1
       grind)
    | exact resolve eq3091 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091
  have eq3133 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq3098 X0 (τ X1)
       grind)
    | exact superpose eq3098 eq17
    | (have j1 := eq3098 X0 (τ X1)
       grind)
    | exact resolve eq17 eq3098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3098
  have eq3188 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3133 X0 X1
       have i₂ := eq378 X1
       grind)
    | exact superpose eq378 eq3133
    | (have j0 := eq3133 X0 X1
       grind)
    | exact resolve eq3133 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq3133
  have eq3534 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3188 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3188
    | (have j0 := eq3188 X1 (σ X0)
       grind)
    | exact resolve eq3188 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3188
  have eq3610 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3534 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3534
    | (have j0 := eq3534 X0 X1
       grind)
    | exact resolve eq3534 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3534
  have eq3617 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3610 X0 X1
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq3610
    | (have j0 := eq3610 X0 X1
       grind)
    | exact resolve eq3610 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3610
  have eq3620 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3617 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3617
    | (have j0 := eq3617 X0 X1
       grind)
    | exact resolve eq3617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3617
  have eq4153 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3074 x y
       grind)
    | exact superpose eq3074 eq16
    | (have j1 := eq3074 x y
       grind)
    | exact resolve eq16 eq3074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074
  have eq4236 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq4153
       have i₂ := eq3620 y x
       grind)
    | exact superpose eq3620 eq4153
    | (have j1 := eq3620 x y
       grind)
    | (have r₁ := eq4153
       have r₂ := eq3620 y x
       grind)
    | exact resolve eq4153 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620 eq4153
  have eq4237 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4236
  have eq4268 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y y
       have i₂ := eq4237
       grind)
    | exact superpose eq4237 eq61
    | exact resolve eq61 eq4237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4269 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq4237
       grind)
    | exact superpose eq4237 eq61
    | exact resolve eq61 eq4237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4237
  have eq4287 : (M.op x x) = (M.op y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67 x (M.op x y) x
       have i₂ := eq4268 x
       grind)
    | exact superpose eq4268 eq67
    | exact resolve eq67 eq4268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4268
  have eq4319 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4269 x
       have i₂ := eq4287
       grind)
    | exact superpose eq4287 eq4269
    | exact resolve eq4269 eq4287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4269 eq4287
  have eq4338 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4319
  have eq4339 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4338
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq4338
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq4338
    | exact resolve eq4338 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4338
  have eq4340 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4339
       grind)
    | exact superpose eq4339 eq16
    | exact resolve eq16 eq4339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4339
  have eq4341 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4340
       have r₂ := eq384 x
       grind)
    | exact resolve eq4340 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4340
  have eq4370 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq384 (M.op y y)
       have i₂ := eq4341
       grind)
    | exact superpose eq4341 eq384
    | exact resolve eq384 eq4341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq4409 : (σ (M.op (M.op y y) (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq4370
       have i₂ := eq384 (M.op x x)
       grind)
    | exact superpose eq384 eq4370
    | exact resolve eq4370 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4370
  have eq4427 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq4409
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq4409
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq4409
    | exact resolve eq4409 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4409
  have eq4428 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4427
       have i₂ := eq61 y y y
       grind)
    | (have i₁ := eq4427
       have i₂ := eq61 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq61 eq4427
    | exact resolve eq4427 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq4427
  have eq4429 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4428
       grind)
    | exact superpose eq4428 eq16
    | exact resolve eq16 eq4428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4430 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4428
       grind)
    | exact superpose eq4428 eq10
    | exact resolve eq10 eq4428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4428
  have eq4503 : x = y := by
    first
    | (have i₁ := eq4430
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4430
    | exact resolve eq4430 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4430
  have eq4504 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4429
       have i₂ := eq384 x
       grind)
    | exact superpose eq384 eq4429
    | exact resolve eq4429 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq4429
  have eq4505 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4504
       have i₂ := eq4503
       grind)
    | exact superpose eq4503 eq4504
    | exact resolve eq4504 eq4503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4503 eq4504
  have eq4506 : False := by grind
  exact eq4506

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq62 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq133 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq420 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq98 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq98
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq438 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq420 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq420
    | (have j0 := eq420 X0
       grind)
    | exact resolve eq420 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq420
  have eq439 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq438 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq438
    | (have j0 := eq438 X0
       grind)
    | exact resolve eq438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq440 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq439 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq439 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq439 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq451 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq440 (σ X0)
       grind)
    | exact superpose eq440 eq15
    | exact resolve eq15 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq451 X0
       have i₂ := eq440 X0
       grind)
    | exact superpose eq440 eq451
    | exact resolve eq451 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq451
  have eq517 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ X0) (σ X0)
       have i₂ := eq470 X0
       grind)
    | exact superpose eq470 eq62
    | exact resolve eq62 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131 x y
       grind)
    | exact superpose eq131 eq16
    | (have j1 := eq131 x y
       grind)
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq2428 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq133 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133
    | exact resolve eq133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq2490 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2428 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2428
    | (have j0 := eq2428 X0 X1
       grind)
    | exact resolve eq2428 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428
  have eq11085 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq679
       have i₂ := eq2490 x y
       grind)
    | exact superpose eq2490 eq679
    | (have j1 := eq2490 (σ x) (σ y)
       grind)
    | (have r₁ := eq679
       have r₂ := eq2490 x y
       grind)
    | (have r₁ := eq679
       have r₂ := eq2490 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq679
       have r₂ := eq2490 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq679 eq2490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq11086 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq11085
  have eq11088 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11086
       grind)
    | exact superpose eq11086 eq16
    | exact resolve eq16 eq11086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11086
  have eq11089 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11088
       have r₂ := eq470 x
       grind)
    | exact resolve eq11088 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11088
  have eq11092 : y ≠ y ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq11089
       grind)
    | exact superpose eq11089 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11089
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11089
       grind)
    | exact resolve eq12 eq11089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11094 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y X0
       have i₂ := eq11089
       grind)
    | exact superpose eq11089 eq62
    | exact resolve eq62 eq11089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11089
  have eq11106 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11092
  have eq11561 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11094 (M.op y x)
       have i₂ := eq11094 x
       grind)
    | exact superpose eq11094 eq11094
    | exact resolve eq11094 eq11094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11094
  have eq11582 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq11561
  have eq11589 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq517 y (σ x)
       have i₂ := eq11582
       grind)
    | exact superpose eq11582 eq517
    | exact resolve eq517 eq11582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq11594 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq62 (σ x) (σ y) X0
       have i₂ := eq11582
       grind)
    | exact superpose eq11582 eq62
    | exact resolve eq62 eq11582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq11582
  have eq11738 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq694 x y
       have i₂ := eq11106
       grind)
    | exact superpose eq11106 eq694
    | (have j0 := eq694 x y
       grind)
    | exact resolve eq694 eq11106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq11106
  have eq11759 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11738
  have eq17219 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11594 (σ (M.op y y))
       have i₂ := eq11589
       grind)
    | exact superpose eq11589 eq11594
    | exact resolve eq11594 eq11589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11589 eq11594
  have eq17249 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq17219
  have eq17256 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17249
       have i₂ := eq470 y
       grind)
    | exact superpose eq470 eq17249
    | exact resolve eq17249 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17249
  have eq17266 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17256
       grind)
    | exact superpose eq17256 eq10
    | exact resolve eq10 eq17256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17256
  have eq17343 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17266
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17266
    | exact resolve eq17266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17266
  have eq17355 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17343
       grind)
    | exact superpose eq17343 eq16
    | exact resolve eq16 eq17343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17343
  have eq17397 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq17355
       have r₂ := eq470 x
       grind)
    | exact resolve eq17355 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17355
  have eq17422 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq17397
       grind)
    | exact superpose eq17397 eq10
    | exact resolve eq10 eq17397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17397
  have eq17519 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17422
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq17422
    | exact resolve eq17422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17422
  have eq17520 : y = (M.op y y) := by grind
  clear eq17519
  have eq17938 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11759
       have i₂ := eq17520
       grind)
    | exact superpose eq17520 eq11759
    | exact resolve eq11759 eq17520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11759
  have eq18032 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17938
  have eq19595 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18032
       grind)
    | exact superpose eq18032 eq16
    | exact resolve eq16 eq18032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19610 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq18032
       grind)
    | exact superpose eq18032 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18032
       grind)
    | exact resolve eq12 eq18032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18032
  have eq19630 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq19610
  have eq19633 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19630
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19630
    | exact resolve eq19630 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19630
  have eq19642 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19633
       have i₂ := eq470 y
       grind)
    | exact superpose eq470 eq19633
    | exact resolve eq19633 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19633
  have eq19648 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19642
       have i₂ := eq17520
       grind)
    | exact superpose eq17520 eq19642
    | exact resolve eq19642 eq17520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17520 eq19642
  have eq19662 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2490 x y
       have i₂ := eq19648
       grind)
    | exact superpose eq19648 eq2490
    | (have j0 := eq2490 x y
       grind)
    | exact resolve eq2490 eq19648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2490 eq19648
  have eq19753 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19662
       have r₂ := eq19595
       grind)
    | exact resolve eq19662 eq19595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19662
  have eq20544 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19595
       have i₂ := eq19753
       grind)
    | exact superpose eq19753 eq19595
    | exact resolve eq19595 eq19753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19595 eq19753
  have eq20578 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20544
  have eq20579 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq20578
  have eq20600 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20579
       grind)
    | exact superpose eq20579 eq10
    | exact resolve eq10 eq20579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20579
  have eq20694 : x = y ∨ x = y := by
    first
    | (have i₁ := eq20600
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20600
    | exact resolve eq20600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20600
  have eq20695 : x = y := by grind
  clear eq20694
  have eq20705 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20695
       grind)
    | exact superpose eq20695 eq16
    | exact resolve eq16 eq20695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20695
  have eq20799 : False := by grind
  exact eq20799
