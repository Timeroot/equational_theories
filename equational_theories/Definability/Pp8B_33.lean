import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (k X0 X1) (M.op X0 X0)
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (k X0 X1)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq176 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : x = (M.op (M.op (M.op x y) x) (k x x)) := by
    first
    | (have i₁ := eq176 x
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq176
    | exact resolve eq176 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq200 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq177 sF2
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq411 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x x) := by
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
  have eq425 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq451 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq425
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq425
    | exact resolve eq425 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq465 : (M.op x y) = (k y x) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq411
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq411
    | exact resolve eq411 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq1385 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 x X0 X1 y
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1392 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq178
    | (have j0 := eq178 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq178 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1481 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1 x (M.op X1 X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1832 : y = (M.op (M.op x y) (M.op (M.op x x) y)) := by
    first
    | exact superpose eq188 eq1385
    | exact resolve eq1385 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq1385
  have eq1897 : y = (M.op (M.op x y) (M.op (k x x) y)) := by
    first
    | (have i₁ := eq1832
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1832
    | exact resolve eq1832 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832
  have eq2038 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y))) := by
    first
    | exact superpose eq200 eq1392
    | exact resolve eq1392 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq1392
  have eq2107 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (k (σ x) (σ x)) (σ y))) := by
    first
    | (have i₁ := eq2038
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq2038
    | exact resolve eq2038 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq2306 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq183 X1 (M.op X0 X1)
       have i₂ := eq1481 X1 X0
       grind)
    | exact superpose eq1481 eq183
    | exact resolve eq183 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1481
  have eq2338 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2306 X0 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq2306
    | exact resolve eq2306 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306
  have eq2437 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2338 X0
       have i₂ := eq175 (k X0 X0)
       grind)
    | exact superpose eq175 eq2338
    | exact resolve eq2338 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338
  have eq2673 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq465
       grind)
    | exact superpose eq465 eq40
    | exact resolve eq40 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq2674 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2673
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2673
    | exact resolve eq2673 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673
  have eq2676 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq2674
    | exact resolve eq2674 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674
  have eq20145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq2676 eq451
    | exact resolve eq451 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq2676
  have eq20154 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq20145
       have r₂ := eq27
       grind)
    | exact resolve eq20145 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20145
  have eq20168 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq20154 eq142
    | exact resolve eq142 eq20154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq20154
  have eq20197 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq30 eq20168
    | exact resolve eq20168 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20168
  have eq20198 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20197
  have eq20210 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1897
       have i₂ := eq20198
       grind)
    | exact superpose eq20198 eq1897
    | exact resolve eq1897 eq20198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq20214 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq20198
       grind)
    | exact superpose eq20198 eq40
    | exact resolve eq40 eq20198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20198
  have eq20243 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20214
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20214
    | exact resolve eq20214 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20214
  have eq20245 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20210
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20210
    | exact resolve eq20210 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20210
  have eq20247 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20245
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq20245
    | exact resolve eq20245 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20245
  have eq20255 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20243 eq2107
    | exact resolve eq2107 eq20243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107 eq20243
  have eq20290 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq20255
    | exact resolve eq20255 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20255
  have eq20293 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20290
       have i₂ := eq175 sF4
       grind)
    | exact superpose eq175 eq20290
    | exact resolve eq20290 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20290
  have eq20329 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20247 eq2437
    | exact resolve eq2437 eq20247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20247
  have eq20379 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20293 eq2437
    | exact resolve eq2437 eq20293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2437 eq20293
  have eq20634 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20379 eq116
    | exact resolve eq116 eq20379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq20379
  have eq20683 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20329 eq20634
    | exact resolve eq20634 eq20329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20329 eq20634
  have eq20686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20683 eq14
    | exact resolve eq14 eq20683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20683
  have eq20697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq20686
    | exact resolve eq20686 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20686
  have eq20700 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20697
       have r₂ := eq27
       grind)
    | exact resolve eq20697 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20697
  have eq20702 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq20700 eq32
    | exact resolve eq32 eq20700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq20700
  have eq20804 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq20702
    | exact resolve eq20702 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20702
  have eq20805 : x = y := by grind
  clear eq20804
  have eq20887 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20805
       grind)
    | exact superpose eq20805 eq18
    | exact resolve eq18 eq20805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20888 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq20805
       grind)
    | exact superpose eq20805 eq24
    | exact resolve eq24 eq20805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq20805
  have eq20974 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20888
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20888
    | exact resolve eq20888 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20888
  have eq20975 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq20887
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq20887
    | exact resolve eq20887 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20887
  have eq20977 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20974 eq26
    | exact resolve eq26 eq20974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq20974
  have eq21081 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq20977
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq20977
    | exact resolve eq20977 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq20977
  have eq21094 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq20975
       grind)
    | exact superpose eq20975 eq40
    | exact resolve eq40 eq20975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq20975
  have eq21120 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21094
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21094
    | exact resolve eq21094 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21094
  have eq21126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21081 eq21120
    | exact resolve eq21120 eq21081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21081 eq21120
  have eq21128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq21126
    | exact resolve eq21126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq21126
  have eq21130 : False := by grind
  exact eq21130

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq412 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq412
    | (have j0 := eq412 X0 X1
       grind)
    | exact resolve eq412 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq640 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq429 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq429
    | exact resolve eq429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq657 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq640 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq640
    | (have j0 := eq640 X0 X1
       grind)
    | exact resolve eq640 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq640
  have eq663 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq657 X0 X1
       have j1 := eq93 X1 X0
       grind)
    | (have r₁ := eq657 X1 X0
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq657 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq657 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq657
  have eq666 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq663
    | exact resolve eq663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq663 (σ X1) X0
       grind)
    | exact superpose eq663 eq15
    | (have j1 := eq663 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq708 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq666 (τ X0) X1
       grind)
    | exact superpose eq666 eq20
    | (have j1 := eq666 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq20 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq666
  have eq788 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq708 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq708
    | exact resolve eq708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq831 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq788 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq788
    | (have j0 := eq788 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq788 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq993 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq678 x y
       grind)
    | exact superpose eq678 eq16
    | (have j1 := eq678 x y
       grind)
    | exact resolve eq16 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq1015 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq993
       have i₂ := eq831 x y
       grind)
    | exact superpose eq831 eq993
    | (have j1 := eq831 (σ x) (σ y)
       grind)
    | (have r₁ := eq993
       have r₂ := eq831 x y
       grind)
    | (have r₁ := eq993
       have r₂ := eq831 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq993
       have r₂ := eq831 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq993 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq993
  have eq1016 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1015
  have eq1019 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1016
       grind)
    | exact superpose eq1016 eq16
    | exact resolve eq16 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1020 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1019
       have r₂ := eq77 x
       grind)
    | exact resolve eq1019 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1021 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1020
       grind)
    | exact superpose eq1020 eq16
    | exact resolve eq16 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1020
       grind)
    | exact superpose eq1020 eq10
    | exact resolve eq10 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1068 : x = y := by
    first
    | (have i₁ := eq1022
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1022
    | exact resolve eq1022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1069 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1021
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq1021
    | exact resolve eq1021 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1021
  have eq1070 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1069
       have i₂ := eq1068
       grind)
    | exact superpose eq1068 eq1069
    | exact resolve eq1069 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068 eq1069
  have eq1071 : False := by grind
  exact eq1071

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ X0 ∨ (k X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X0 X1))) = X0 ∨ (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X0 X1))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X0 X1))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X0 X1))) = X0 ∨ (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq55 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq32 X0 X1
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq32 X0 X1
       grind)
    | exact resolve eq54 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq54
  have eq57 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op (σ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op X1 (M.op (σ X0) X1))
       have i₂ := eq55 (σ X0) X1
       grind)
    | exact superpose eq55 eq29
    | exact resolve eq29 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq60 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (M.op (σ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57
    | exact resolve eq57 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq110 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op (σ (σ X0)) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (τ (M.op X1 (M.op (σ (σ X0)) X1)))
       have i₂ := eq60 (σ X0) X1
       grind)
    | exact superpose eq60 eq29
    | exact resolve eq29 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq119 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 (M.op (σ (σ X0)) X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq110
    | exact resolve eq110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq164 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 (M.op (σ (σ (σ X0))) X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (τ (τ (M.op X1 (M.op (σ (σ (σ X0))) X1))))
       have i₂ := eq119 (σ X0) X1
       grind)
    | exact superpose eq119 eq29
    | exact resolve eq29 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq173 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (M.op X1 (M.op (σ (σ (σ X0))) X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq164 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq164
    | exact resolve eq164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq239 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq250 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq667 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ X0)))) X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ X0)))) X1)))))
       have i₂ := eq173 (σ X0) X1
       grind)
    | exact superpose eq173 eq29
    | exact resolve eq29 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq678 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ X0)))) X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq667 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq667
    | exact resolve eq667 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq806 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ X0))))) X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ X0))))) X1))))))
       have i₂ := eq678 (σ X0) X1
       grind)
    | exact superpose eq678 eq29
    | exact resolve eq29 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq817 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ X0))))) X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq806
    | exact resolve eq806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq1040 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq250 (τ X1) (τ X0)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq250
    | (have j0 := eq250 (τ X1) (τ X0)
       grind)
    | exact resolve eq250 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq1062 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1040 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1040
    | (have j0 := eq1040 X0 X1
       grind)
    | exact resolve eq1040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1070 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1062 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1062
    | (have j0 := eq1062 X0 X1
       grind)
    | exact resolve eq1062 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1075 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1070 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1070
    | (have j0 := eq1070 X0 X1
       grind)
    | exact resolve eq1070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1076 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1075 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1075
    | (have j0 := eq1075 X0 X1
       grind)
    | exact resolve eq1075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1077 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1076
    | (have j0 := eq1076 X0 X1
       grind)
    | exact resolve eq1076 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1078 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1077
    | (have j0 := eq1077 X0 X1
       grind)
    | exact resolve eq1077 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1467 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ X0)))))) X1))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ X0)))))) X1)))))))
       have i₂ := eq817 (σ X0) X1
       grind)
    | exact superpose eq817 eq29
    | exact resolve eq29 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq817
  have eq1488 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ X0)))))) X1))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1467 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1467
    | exact resolve eq1467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq3162 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq239 X0 X1 X2
       grind)
    | exact superpose eq239 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq239 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq239 X0 X1 X2
       grind)
    | exact resolve eq13 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3170 : ∀ X0 X1 X2 : G, (σ X0) ≠ (k (σ X1) X2) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq239 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq3171 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3162 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162
  have eq3172 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3171 X0 X1 X2
       have j1 := eq3170 X2 X0 X1
       grind)
    | (have r₁ := eq3171 X1 X2 X0
       have r₂ := eq3170 X0 X1 X2
       grind)
    | exact resolve eq3171 eq3170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3170 eq3171
  have eq3207 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3172 X0 X1 X2
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq3172
    | (have j0 := eq3172 X0 X1 X2
       grind)
    | exact resolve eq3172 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3172
  have eq52541 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (k X0 X2)) ∨ (σ (k (k (τ X0) (τ X2)) X1)) = (M.op (σ X1) (k X0 X2)) ∨ (k X0 X2) = (σ (k (k (τ X0) (τ X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3207 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3207
    | exact resolve eq3207 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3207
  have eq52780 : ∀ X0 X1 X2 : G, (M.op (σ X1) (k X0 X2)) = (σ (k (τ (k X0 X2)) X1)) ∨ (σ X1) = (M.op (σ X1) (k X0 X2)) ∨ (k X0 X2) = (σ (k (k (τ X0) (τ X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52541 X0 X1 X2
       have i₂ := eq33 X2 X0
       grind)
    | exact superpose eq33 eq52541
    | (have j0 := eq52541 X0 X1 X2
       grind)
    | exact resolve eq52541 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52541
  have eq52899 : ∀ X0 X1 X2 : G, (M.op (σ X1) (k X0 X2)) = (k (k X0 X2) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (k X0 X2)) ∨ (k X0 X2) = (σ (k (k (τ X0) (τ X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52780 X0 X1 X2
       have i₂ := eq18 (k X0 X2) X1
       grind)
    | exact superpose eq18 eq52780
    | (have j0 := eq52780 X0 X1 X2
       grind)
    | exact resolve eq52780 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52780
  have eq52999 : ∀ X0 X1 X2 : G, (M.op (σ X1) (k X0 X2)) = (k (k X0 X2) (σ X1)) ∨ (k X0 X2) = (σ (k (k (τ X0) (τ X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq52899 X0 X1 X2
       have j1 := eq12 (k X0 X2) (σ X1)
       grind)
    | (have r₁ := eq52899 X0 X1 X2
       have r₂ := eq12 (k X0 X2) (σ X1)
       grind)
    | exact resolve eq52899 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52899
  have eq53077 : ∀ X0 X1 X2 : G, (k X0 X2) = (σ (k (τ (k X0 X2)) X1)) ∨ (M.op (σ X1) (k X0 X2)) = (k (k X0 X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52999 X0 X1 X2
       have i₂ := eq33 X2 X0
       grind)
    | exact superpose eq33 eq52999
    | (have j0 := eq52999 X0 X1 X2
       grind)
    | exact resolve eq52999 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq52999
  have eq53132 : ∀ X0 X1 X2 : G, (k X0 X2) = (k (k X0 X2) (σ X1)) ∨ (M.op (σ X1) (k X0 X2)) = (k (k X0 X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53077 X0 X1 X2
       have i₂ := eq18 (k X0 X2) X1
       grind)
    | exact superpose eq18 eq53077
    | (have j0 := eq53077 X0 X1 X2
       grind)
    | exact resolve eq53077 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53077
  have eq345051 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op (σ X2) (k X0 X1)) ∨ (σ X2) = (M.op (σ X2) (k X0 X1)) ∨ (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1078 (k X0 X1) (σ X2)
       have i₂ := eq53132 X0 X2 X1
       grind)
    | exact superpose eq53132 eq1078
    | (have j0 := eq1078 (k X0 X1) (σ X2)
       have j1 := eq53132 X0 X2 X1
       grind)
    | (have r₁ := eq1078 (k X0 X2) (σ X1)
       have r₂ := eq53132 X0 X1 X2
       grind)
    | exact resolve eq1078 eq53132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq345074 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (M.op (σ X2) (k X0 X1)) ∨ (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq53132 X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53132
  have eq345077 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (σ X2) (k X0 X1)) ∨ (σ X2) = (M.op (σ X2) (k X0 X1)) ∨ (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq345051 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345051
  have eq345099 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k X0 X1)) ∨ (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq345077 X0 X1 X2
       have j1 := eq345074 X0 X1 X2
       grind)
    | (have r₁ := eq345077 X0 X1 X2
       have r₂ := eq345074 X0 X1 X2
       grind)
    | exact resolve eq345077 eq345074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345074 eq345077
  have eq345153 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq345099 X0 X1 X2
       have j1 := eq12 (k X0 X1) (σ X2)
       grind)
    | (have r₁ := eq345099 X0 X1 X2
       have r₂ := eq12 (k X0 X1) (σ X2)
       grind)
    | exact resolve eq345099 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345099
  have eq345960 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq345153 X0 (τ (τ (τ (τ (τ (τ (M.op x (M.op (σ (σ (σ (σ (σ (σ X0)))))) x)))))))) X2
       have i₂ := eq1488 X0 x
       grind)
    | exact superpose eq1488 eq345153
    | exact resolve eq345153 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488 eq345153
  have eq347754 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345960 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345960
    | exact resolve eq345960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350058 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq347754 X0 (τ X1)
       grind)
    | exact superpose eq347754 eq18
    | exact resolve eq18 eq347754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq347754
  have eq350270 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq350058 X0 X1
       have i₂ := eq345960 X1 X0
       grind)
    | exact superpose eq345960 eq350058
    | exact resolve eq350058 eq345960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345960 eq350058
  have eq360032 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq350270 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq350270
    | exact resolve eq350270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350270
  have eq378294 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq360032 y x
       grind)
    | exact superpose eq360032 eq16
    | (have r₁ := eq16
       have r₂ := eq360032 y x
       grind)
    | exact resolve eq16 eq360032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360032
  have eq378520 : False := by grind
  exact eq378520

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation221 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X1)) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq39 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k X1 (τ X0))
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq23
    | exact resolve eq23 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq53 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq10
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 (τ X0) (τ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq18
    | exact resolve eq18 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq166 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 (k X1 (τ X0))
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq54
    | exact resolve eq54 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq178 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq166 X0 X1 X2
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq166
    | (have j0 := eq166 X0 X1 X2
       grind)
    | exact resolve eq166 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq166
  have eq1438 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op (τ X0) X1)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op X1 (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 (M.op (τ X1) X1)) X1
       have i₂ := eq9 (τ X1) X1
       grind)
    | exact superpose eq9 eq53
    | (have j0 := eq53 (M.op (τ X0) (τ X0)) X0
       grind)
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1501 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (M.op (τ X0) X1)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op X1 (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1438 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1438
    | (have j0 := eq1438 X0 X1
       grind)
    | exact resolve eq1438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq1511 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op (τ X0) X1)) ∨ (k X0 (σ (M.op X1 (M.op (τ X0) X1)))) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1501 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq1501
    | (have j0 := eq1501 X0 X1
       grind)
    | exact resolve eq1501 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq4663 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (k (k (σ X1) X2) X3) = (M.op (σ X0) (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq178 X0 X1 X2
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 (k (k (σ X1) X2) X3) (M.op (σ X0) (k (σ X1) X2))
       have j1 := eq178 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq178 X0 X1 X2
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq17935 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (M.op X1 (M.op (τ X0) X1)))) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq1511 X0 X1
       grind)
    | exact superpose eq1511 eq9
    | (have j1 := eq1511 X0 X1
       grind)
    | exact resolve eq9 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq17958 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op X1 (M.op (τ X0) X1)))) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17935 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq17935
    | (have j0 := eq17935 X0 X1
       grind)
    | exact resolve eq17935 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17935
  have eq17959 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op X1 (M.op (τ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17958 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17958
  have eq18000 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X0 (σ (M.op X1 (M.op (τ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq17959 X0 X1
       grind)
    | exact superpose eq17959 eq11
    | (have j1 := eq17959 X0 X1
       grind)
    | exact resolve eq11 eq17959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17959
  have eq18145 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ (M.op X1 (M.op (τ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18000 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18000
    | (have j0 := eq18000 X0 X1
       grind)
    | exact resolve eq18000 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18000
  have eq18226 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (σ (M.op X1 (M.op (τ (τ X0)) X1)))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0
       have i₂ := eq18145 (τ X0) X1
       grind)
    | exact superpose eq18145 eq75
    | (have j1 := eq18145 (τ X0) X1
       grind)
    | exact resolve eq75 eq18145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18145
  have eq21672 : ∀ X0 X1 : G, (τ (τ X0)) = (k (τ (τ X0)) (M.op X1 (M.op (τ (τ X0)) X1))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (τ X0) (M.op X1 (M.op (τ (τ X0)) X1))
       have i₂ := eq18226 X0 X1
       grind)
    | exact superpose eq18226 eq29
    | (have j1 := eq18226 X0 X1
       grind)
    | exact resolve eq29 eq18226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18226
  have eq38482 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (M.op X1 (M.op (τ X0) X1))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21672 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21672
    | exact resolve eq21672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21672
  have eq38633 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X0 ∨ (τ X0) = (k (τ X0) (M.op X1 (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38482 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq38482
    | (have j0 := eq38482 X0 X1
       grind)
    | exact resolve eq38482 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38482
  have eq38677 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (M.op X1 (M.op (τ X0) X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38633 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq38633
    | (have j0 := eq38633 X0 X1
       grind)
    | exact resolve eq38633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38633
  have eq38807 : ∀ X0 : G, (τ X0) = (k (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq38677 X0 (τ (M.op X0 X0))
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq38677
    | (have j0 := eq38677 X0 x
       grind)
    | exact resolve eq38677 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq38677
  have eq40419 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ (M.op X0 X0))))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ (M.op X0 X0)))
       have i₂ := eq38807 X0
       grind)
    | exact superpose eq38807 eq19
    | (have j1 := eq38807 X0
       grind)
    | exact resolve eq19 eq38807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38807
  have eq40513 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ (M.op (τ X0) (τ (M.op X0 X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq40419 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40419
    | (have j0 := eq40419 X0
       grind)
    | exact resolve eq40419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40419
  have eq40662 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ X0) = (k (τ X0) (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq40513 (τ X0)
       grind)
    | exact superpose eq40513 eq31
    | (have j1 := eq40513 (τ X0)
       grind)
    | exact resolve eq31 eq40513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq40513
  have eq40746 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (k (τ X0) (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq40662 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40662
    | (have j0 := eq40662 X0
       grind)
    | exact resolve eq40662 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40662
  have eq40791 : ∀ X0 : G, (τ X0) = (k (τ X0) (σ (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40746 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq40746
    | (have j0 := eq40746 X0
       grind)
    | exact resolve eq40746 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq40746
  have eq57703 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ (M.op X0 X0))))))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))))
       have i₂ := eq40791 X0
       grind)
    | exact superpose eq40791 eq19
    | (have j1 := eq40791 X0
       grind)
    | exact resolve eq19 eq40791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq40791
  have eq57854 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ (M.op X0 X0))))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57703 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57703
    | (have j0 := eq57703 X0
       grind)
    | exact resolve eq57703 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57703
  have eq245409 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4663 X2 X0 X1 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4663
  have eq245410 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq245409 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245409
  have eq245413 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq245410 X0 X1 X2
       have i₂ := eq39 X0 X1 X2
       grind)
    | exact superpose eq39 eq245410
    | (have j0 := eq245410 X0 X1 X2
       grind)
    | exact resolve eq245410 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq245410
  have eq245414 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq245413 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245413
  have eq245895 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 (k X1 (τ X2))
       have i₂ := eq245414 X1 X2 (τ X0)
       grind)
    | exact superpose eq245414 eq20
    | (have j1 := eq245414 X1 X2 (τ X0)
       grind)
    | exact resolve eq20 eq245414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245414
  have eq246290 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq245895 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq245895
    | (have j0 := eq245895 X0 X1 X2
       grind)
    | exact resolve eq245895 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245895
  have eq246428 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq246290 X0 X1 X2
       have i₂ := eq20 X2 X1
       grind)
    | exact superpose eq20 eq246290
    | (have j0 := eq246290 X0 X1 X2
       grind)
    | exact resolve eq246290 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246290
  have eq246538 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq246428 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246428
    | (have j0 := eq246428 X0 X1 X2
       grind)
    | exact resolve eq246428 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246428
  have eq246775 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) ∨ (k X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq246538 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246538
    | exact resolve eq246538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246538
  have eq248131 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq248154 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq246775 X0 (σ (σ (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))))) x
       have i₂ := eq57854 X0
       grind)
    | exact superpose eq57854 eq246775
    | (have j0 := eq246775 X0 X1 (M.op X1 X0)
       have j1 := eq57854 X0
       grind)
    | exact resolve eq246775 eq57854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57854 eq246775
  have eq250255 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq248131 X0 X1
       have i₂ := eq248154 X0 X1
       grind)
    | exact superpose eq248154 eq248131
    | (have j1 := eq248154 X0 X1
       grind)
    | exact resolve eq248131 eq248154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248131 eq248154
  have eq366525 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq250255 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250255
  have eq366526 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq366525 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366525
  have eq366527 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq366526 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366526
  have eq366930 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq366527 X1 (τ X0)
       grind)
    | exact superpose eq366527 eq20
    | (have j1 := eq366527 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq20 eq366527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq367280 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq366527 (σ X1) (σ X0)
       grind)
    | exact superpose eq366527 eq15
    | (have j1 := eq366527 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq366527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366527
  have eq370891 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq366930 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq366930
    | exact resolve eq366930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366930
  have eq371478 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq370891 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq370891
    | (have j0 := eq370891 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq370891 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370891
  have eq375893 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq367280 x y
       grind)
    | exact superpose eq367280 eq16
    | (have j1 := eq367280 x y
       grind)
    | exact resolve eq16 eq367280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367280
  have eq376061 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq375893
       have i₂ := eq371478 x y
       grind)
    | exact superpose eq371478 eq375893
    | (have j1 := eq371478 (σ x) (σ y)
       grind)
    | (have r₁ := eq375893
       have r₂ := eq371478 x y
       grind)
    | (have r₁ := eq375893
       have r₂ := eq371478 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq375893
       have r₂ := eq371478 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq375893 eq371478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371478 eq375893
  have eq376064 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq376061
  have eq377830 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq376064
       grind)
    | exact superpose eq376064 eq16
    | exact resolve eq16 eq376064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376064
  have eq377831 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq377830
       have r₂ := eq23 x
       grind)
    | exact resolve eq377830 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377830
  have eq377832 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq377831
       grind)
    | exact superpose eq377831 eq16
    | exact resolve eq16 eq377831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377833 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq377831
       grind)
    | exact superpose eq377831 eq10
    | exact resolve eq10 eq377831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377831
  have eq378327 : x = y := by
    first
    | (have i₁ := eq377833
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq377833
    | exact resolve eq377833 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377833
  have eq378328 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq377832
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq377832
    | exact resolve eq377832 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq377832
  have eq378333 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq378328
       have i₂ := eq378327
       grind)
    | exact superpose eq378327 eq378328
    | exact resolve eq378328 eq378327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378327 eq378328
  have eq378334 : False := by grind
  exact eq378334

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation2291 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq77 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq86
  have eq221 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq229 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq221 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq233 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq229 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq229 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq229 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq243 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       have j1 := eq77 X0 (σ X1)
       grind)
    | (have r₁ := eq233 X0 X1
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq233 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq233
  have eq250 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq243
    | (have j0 := eq243 X0 X1
       grind)
    | exact resolve eq243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq251 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq255 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq251 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq251
    | exact resolve eq251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq251 x y
       grind)
    | exact superpose eq251 eq16
    | exact resolve eq16 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq330 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq255 X0 (τ X1)
       grind)
    | exact superpose eq255 eq17
    | exact resolve eq17 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq255
  have eq350 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq330
    | exact resolve eq330 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq360 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq350
    | exact resolve eq350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq377 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq266
       have i₂ := eq360 x y
       grind)
    | exact superpose eq360 eq266
    | exact resolve eq266 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq360
  have eq378 : False := by grind
  exact eq378

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation2291 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 x y
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : (k y y) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq563
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq563
    | exact resolve eq563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq1225 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 y x
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq1225
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1225
    | exact resolve eq1225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1245 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1235
       have i₂ := eq21 (σ y) (σ x)
       grind)
    | exact superpose eq21 eq1235
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1235
       have r₂ := eq21 (σ y) (σ x)
       grind)
    | (have r₁ := eq1235
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1235
       have r₂ := eq21 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1235 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1235
  have eq1247 : x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1245
  have eq1323 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1247
       grind)
    | exact superpose eq1247 eq9
    | exact resolve eq9 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1324 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1323
  have eq1325 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1324
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1324
    | exact resolve eq1324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1326 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1325
  have eq1327 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1326
  have eq1405 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1327
       grind)
    | exact superpose eq1327 eq10
    | exact resolve eq10 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1407 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1405
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1405
    | exact resolve eq1405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1408 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1407
  have eq1411 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq22
    | exact resolve eq22 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1458 : (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1411
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1411
    | exact resolve eq1411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1411
  have eq1480 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq570
       have i₂ := eq1458
       grind)
    | exact superpose eq1458 eq570
    | (have r₁ := eq570
       have r₂ := eq1458
       grind)
    | exact resolve eq570 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq1458
  have eq1483 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1480
  have eq1487 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1483
       have i₂ := eq20 (σ x) (σ y)
       grind)
    | exact superpose eq20 eq1483
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1483
       have r₂ := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1483
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1483
       have r₂ := eq20 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1483 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1483
  have eq1488 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1487
  have eq1489 : x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1488
  have eq1491 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1489
       have r₂ := eq1408
       grind)
    | exact resolve eq1489 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq1489
  have eq1492 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1491
       grind)
    | exact superpose eq1491 eq9
    | exact resolve eq9 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1493 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1492
  have eq1494 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1493
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1493
    | exact resolve eq1493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1495 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1494
  have eq1496 : (σ x) = (σ y) := by grind
  clear eq1495
  have eq1498 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq15
    | exact resolve eq15 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1545 : x = y := by
    first
    | (have i₁ := eq1498
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1498
    | exact resolve eq1498 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1548 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1545
       grind)
    | exact superpose eq1545 eq9
    | exact resolve eq9 eq1545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq1549 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1548
  have eq1550 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1549
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1549
    | exact resolve eq1549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1551 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1550
  have eq1552 : False := by grind
  exact eq1552

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation2291 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2291 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 y x
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : (k x x) ≠ (k y y) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq563
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq563
    | exact resolve eq563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq1225 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 x y
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq1225
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1225
    | exact resolve eq1225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1245 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1235
       have i₂ := eq21 (σ x) (σ y)
       grind)
    | exact superpose eq21 eq1235
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1235
       have r₂ := eq21 (σ x) (σ y)
       grind)
    | (have r₁ := eq1235
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1235
       have r₂ := eq21 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1235 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1235
  have eq1247 : x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1245
  have eq1323 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1247
       grind)
    | exact superpose eq1247 eq9
    | exact resolve eq9 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1324 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1323
  have eq1325 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1324
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1324
    | exact resolve eq1324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1326 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1325
  have eq1327 : (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1326
  have eq1405 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1327
       grind)
    | exact superpose eq1327 eq10
    | exact resolve eq10 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1407 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1405
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1405
    | exact resolve eq1405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1408 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1407
  have eq1412 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq22
    | exact resolve eq22 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1459 : (k x x) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1412
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1412
    | exact resolve eq1412 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1412
  have eq1481 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq570
       have i₂ := eq1459
       grind)
    | exact superpose eq1459 eq570
    | (have r₁ := eq570
       have r₂ := eq1459
       grind)
    | exact resolve eq570 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq1459
  have eq1484 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1481
  have eq1488 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1484
       have i₂ := eq20 (σ y) (σ x)
       grind)
    | exact superpose eq20 eq1484
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1484
       have r₂ := eq20 (σ y) (σ x)
       grind)
    | (have r₁ := eq1484
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1484
       have r₂ := eq20 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1484 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1484
  have eq1489 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1488
  have eq1490 : x = y ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1489
  have eq1492 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1490
       have r₂ := eq1408
       grind)
    | exact resolve eq1490 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq1490
  have eq1493 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1492
       grind)
    | exact superpose eq1492 eq9
    | exact resolve eq9 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1494 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1493
  have eq1495 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1494
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1494
    | exact resolve eq1494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq1496 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1495
  have eq1497 : (σ x) = (σ y) := by grind
  clear eq1496
  have eq1499 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1497
       grind)
    | exact superpose eq1497 eq15
    | exact resolve eq15 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1546 : x = y := by
    first
    | (have i₁ := eq1499
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1499
    | exact resolve eq1499 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1549 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1546
       grind)
    | exact superpose eq1546 eq9
    | exact resolve eq9 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq1550 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1549
  have eq1551 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1550
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1550
    | exact resolve eq1550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq1552 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1551
  have eq1553 : False := by grind
  exact eq1553

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation2291 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2291 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq461 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq464 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq653 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq464 x y
       grind)
    | exact superpose eq464 eq16
    | (have j1 := eq464 x y
       grind)
    | exact resolve eq16 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq464 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq3530 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq461
    | exact resolve eq461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq3591 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3530 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3530
    | (have j0 := eq3530 X0 X1
       grind)
    | exact resolve eq3530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530
  have eq7197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq653
       have i₂ := eq3591 y x
       grind)
    | exact superpose eq3591 eq653
    | (have j1 := eq3591 (σ x) (σ y)
       grind)
    | (have r₁ := eq653
       have r₂ := eq3591 y x
       grind)
    | (have r₁ := eq653
       have r₂ := eq3591 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq653
       have r₂ := eq3591 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq653 eq3591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7198 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq7197
  have eq14414 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) ≠ (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq660 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq660
    | exact resolve eq660 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq14441 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14414 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq14414
    | (have j0 := eq14414 X0 X1
       grind)
    | exact resolve eq14414 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq14414
  have eq14446 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14441 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14441
    | exact resolve eq14441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14441
  have eq19795 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7198
       grind)
    | exact superpose eq7198 eq16
    | exact resolve eq16 eq7198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7198
  have eq19796 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq19795
       have r₂ := eq22 x
       grind)
    | exact resolve eq19795 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19795
  have eq19798 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19796
       grind)
    | exact superpose eq19796 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19796
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19796
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19796
       grind)
    | exact resolve eq13 eq19796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19796
  have eq19799 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq19798
  have eq20125 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19799
       grind)
    | exact superpose eq19799 eq16
    | exact resolve eq16 eq19799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19799
  have eq20126 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq20125
       have r₂ := eq22 x
       grind)
    | exact resolve eq20125 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20125
  have eq20128 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq20126
       grind)
    | exact superpose eq20126 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20126
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20126
       grind)
    | exact resolve eq13 eq20126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20126
  have eq20132 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq20128
  have eq20133 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq20132
  have eq20136 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq20133
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq20133
    | exact resolve eq20133 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20133
  have eq20167 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20136
       grind)
    | exact superpose eq20136 eq16
    | exact resolve eq16 eq20136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20136
  have eq20193 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq20167
       have i₂ := eq3591 y x
       grind)
    | exact superpose eq3591 eq20167
    | (have j1 := eq3591 x y
       grind)
    | (have r₁ := eq20167
       have r₂ := eq3591 y x
       grind)
    | (have r₁ := eq20167
       have r₂ := eq3591 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq20167
       have r₂ := eq3591 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq20167 eq3591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3591 eq20167
  have eq20194 : (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq20193
  have eq20196 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq14446 x y
       grind)
    | (have r₁ := eq20194
       have r₂ := eq14446 x y
       grind)
    | exact resolve eq20194 eq14446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14446 eq20194
  have eq20198 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20196
       grind)
    | exact superpose eq20196 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20196
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20196
       grind)
    | exact resolve eq13 eq20196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20199 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq20196
       grind)
    | exact superpose eq20196 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20196
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20196
       grind)
    | exact resolve eq13 eq20196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20196
  have eq20200 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq20199
  have eq20201 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq20200
  have eq20202 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq20198
  have eq20203 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq20202
  have eq20211 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20201
       grind)
    | exact superpose eq20201 eq16
    | exact resolve eq16 eq20201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20201
  have eq20212 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20211
       have r₂ := eq22 x
       grind)
    | exact resolve eq20211 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20211
  have eq20260 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20203
       grind)
    | exact superpose eq20203 eq16
    | exact resolve eq16 eq20203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20203
  have eq20261 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20260
       have r₂ := eq22 x
       grind)
    | exact resolve eq20260 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20260
  have eq20263 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq653
       have i₂ := eq20261
       grind)
    | exact superpose eq20261 eq653
    | exact resolve eq653 eq20261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq20261
  have eq20267 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq20263
  have eq20268 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq20267
  have eq20273 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq20268
       grind)
    | exact superpose eq20268 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20268
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20268
       grind)
    | exact resolve eq13 eq20268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20268
  have eq20274 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq20273
  have eq20275 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq20274
  have eq20279 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20275
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20275
    | exact resolve eq20275 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20275
  have eq20285 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20279
       grind)
    | exact superpose eq20279 eq16
    | exact resolve eq16 eq20279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20279
  have eq20309 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20285
       have i₂ := eq20212
       grind)
    | exact superpose eq20212 eq20285
    | exact resolve eq20285 eq20212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20212 eq20285
  have eq20312 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq20309
  have eq20313 : (σ x) = (σ y) := by grind
  clear eq20312
  have eq20314 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20313
       grind)
    | exact superpose eq20313 eq16
    | exact resolve eq16 eq20313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20315 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20313
       grind)
    | exact superpose eq20313 eq10
    | exact resolve eq10 eq20313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20313
  have eq20494 : x = y := by
    first
    | (have i₁ := eq20315
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20315
    | exact resolve eq20315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20315
  have eq20495 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20314
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq20314
    | exact resolve eq20314 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20314
  have eq20496 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20495
       have i₂ := eq20494
       grind)
    | exact superpose eq20494 eq20495
    | exact resolve eq20495 eq20494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20494 eq20495
  have eq20497 : False := by grind
  exact eq20497
