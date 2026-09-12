import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_pyx_pxy_pyx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
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
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq139
    | exact resolve eq139 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq139
  have eq168 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq188 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq210 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq214 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq10
    | exact resolve eq10 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq168 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq168
    | exact resolve eq168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq260 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq214 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq214
    | exact resolve eq214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq3335 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
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
  have eq3336 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3335 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3335
  have eq3343 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq81 eq3336
    | exact resolve eq3336 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3347 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq3336
    | (have j0 := eq3336 (σ y) (σ x)
       grind)
    | exact resolve eq3336 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3350 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3336 (M.op X0 X0) X1
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq3336
    | exact resolve eq3336 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq3398 : (k (τ (σ x)) (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3343 eq226
    | exact resolve eq226 eq3343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq3401 : (τ (M.op (σ x) (σ y))) = (k (τ (σ x)) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq3398
       have i₂ := eq260 sF4
       grind)
    | exact superpose eq260 eq3398
    | exact resolve eq3398 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398
  have eq3406 : (τ (M.op (σ x) (σ y))) = (k x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq38 eq3401
    | exact resolve eq3401 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3401
  have eq3431 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq3347 eq226
    | exact resolve eq226 eq3347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq3434 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) (M.op (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq3431
       have i₂ := eq260 sF3
       grind)
    | exact superpose eq260 eq3431
    | exact resolve eq3431 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3431
  have eq3438 : y = (k (τ (M.op (σ x) (σ y))) (M.op y y)) := by
    first
    | exact superpose eq39 eq3434
    | exact resolve eq3434 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3434
  have eq3781 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq210 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq210 X0 X1
       grind)
    | exact superpose eq210 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq210 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq210 X0 X1
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq210 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq210 X0 (τ X0)
       grind)
    | exact resolve eq13 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq3837 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3781 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3781
  have eq3838 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3837 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3837
  have eq3853 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3838 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq3838 X0 (τ X0)
       have r₂ := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq3838 X0 X1
       have r₂ := eq12 (τ X0) X1
       grind)
    | exact resolve eq3838 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3838
  have eq7398 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq38 eq3853
    | (have j0 := eq3853 (σ x) X0
       grind)
    | exact resolve eq3853 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7439 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq3438
       have i₂ := eq3853 sF4 (M.op y y)
       grind)
    | exact superpose eq3853 eq3438
    | (have j1 := eq3853 (M.op (σ x) (σ y)) (M.op y y)
       grind)
    | exact resolve eq3438 eq3853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3853
  have eq7520 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) := by
    first
    | (have i₁ := eq7439
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq7439
    | exact resolve eq7439 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq7439
  have eq7551 : ∀ X0 : G, (σ x) = (σ (k x X0)) ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq31 eq7398
    | (have j0 := eq7398 X0
       grind)
    | exact resolve eq7398 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7398
  have eq7586 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) := by
    first
    | (have i₁ := eq7520
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7520
    | exact resolve eq7520 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7520
  have eq7624 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3347 eq7586
    | exact resolve eq7586 eq3347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3347 eq7586
  have eq8043 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7624 eq53
    | exact resolve eq53 eq7624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7624
  have eq8319 : (σ x) = (σ (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq3406 eq7551
    | exact resolve eq7551 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq8360 : ∀ X0 : G, (k x X0) = (τ (σ x)) ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k x X0)
       have i₂ := eq7551 X0
       grind)
    | exact superpose eq7551 eq10
    | (have j1 := eq7551 X0
       grind)
    | exact resolve eq10 eq7551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8441 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (k x X0) := by
    intro X0
    first
    | exact superpose eq38 eq8360
    | (have j0 := eq8360 X0
       grind)
    | exact resolve eq8360 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8360
  have eq8468 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8319
       have i₂ := eq11 sF4
       grind)
    | exact superpose eq11 eq8319
    | exact resolve eq8319 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8319
  have eq9261 : ∀ X0 : G, x = (M.op (M.op X0 x) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8468 eq53
    | exact resolve eq53 eq8468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq8468
  have eq9275 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9261 eq8043
    | exact resolve eq8043 eq9261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8043 eq9261
  have eq9288 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9275
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9275
    | exact resolve eq9275 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9275
  have eq9299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9288 eq11
    | exact resolve eq11 eq9288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9288
  have eq9337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9299
    | exact resolve eq9299 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9299
  have eq9338 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9337
       have r₂ := eq27
       grind)
    | exact resolve eq9337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9337
  have eq9339 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9338 eq27
    | exact resolve eq27 eq9338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9340 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9338 eq78
    | exact resolve eq78 eq9338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq9341 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9338 eq81
    | exact resolve eq81 eq9338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9353 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9338
  have eq9364 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9340 eq9340
    | exact resolve eq9340 eq9340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9340
  have eq9379 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9364
  have eq9424 : ∀ X0 : G, (σ y) = (k (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9379 eq3350
    | exact resolve eq3350 eq9379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350 eq9379
  have eq11524 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9341 eq9424
    | exact resolve eq9424 eq9341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9341 eq9424
  have eq11543 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11524
  have eq11549 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64 eq11543
    | exact resolve eq11543 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq11543
  have eq11559 : (σ x) = (σ y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7551 y
       have i₂ := eq11549
       grind)
    | exact superpose eq11549 eq7551
    | (have j0 := eq7551 y
       grind)
    | exact resolve eq7551 eq11549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7551
  have eq11621 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11559
       have r₂ := eq9353
       grind)
    | exact resolve eq11559 eq9353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9353 eq11559
  have eq11632 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11621
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11621
    | exact resolve eq11621 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11621
  have eq11680 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11549
       have i₂ := eq11632
       grind)
    | exact superpose eq11632 eq11549
    | exact resolve eq11549 eq11632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11549 eq11632
  have eq11691 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11680
  have eq11698 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11691
    | exact resolve eq11691 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11691
  have eq11706 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11698
       have r₂ := eq9339
       grind)
    | exact resolve eq11698 eq9339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9339 eq11698
  have eq11714 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq11706 eq27
    | exact resolve eq27 eq11706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq11716 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq11706 eq81
    | exact resolve eq81 eq11706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq11730 : y = (k (τ (σ x)) (M.op y y)) := by
    first
    | exact superpose eq11706 eq3438
    | exact resolve eq3438 eq11706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438 eq11706
  have eq11816 : y = (k x (M.op y y)) := by
    first
    | exact superpose eq38 eq11730
    | exact resolve eq11730 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11730
  have eq12002 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11716 eq11716
    | exact resolve eq11716 eq11716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11716
  have eq12319 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq12002 eq260
    | exact resolve eq260 eq12002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq12002
  have eq12339 : x = (M.op x x) := by
    first
    | exact superpose eq38 eq12319
    | exact resolve eq12319 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq12319
  have eq12431 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq54 x x x
       have i₂ := eq12339
       grind)
    | exact superpose eq12339 eq54
    | exact resolve eq54 eq12339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq12917 : y = (M.op x (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq8441 (M.op y y)
       have i₂ := eq11816
       grind)
    | exact superpose eq11816 eq8441
    | exact resolve eq8441 eq11816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8441 eq11816
  have eq14019 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12431 (M.op y y)
       have i₂ := eq12917
       grind)
    | exact superpose eq12917 eq12431
    | exact resolve eq12431 eq12917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12431 eq12917
  have eq14036 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14019
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14019
    | exact resolve eq14019 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14019
  have eq14037 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14036 eq20
    | exact resolve eq20 eq14036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14036
  have eq14074 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14037
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14037
    | exact resolve eq14037 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14037
  have eq14076 : x = y := by
    first
    | (have r₁ := eq14074
       have r₂ := eq11714
       grind)
    | exact resolve eq14074 eq11714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14074
  have eq14077 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14076
       grind)
    | exact superpose eq14076 eq18
    | exact resolve eq18 eq14076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq14076
  have eq15520 : x = (M.op x y) := by
    first
    | (have i₁ := eq14077
       have i₂ := eq12339
       grind)
    | exact superpose eq12339 eq14077
    | exact resolve eq14077 eq12339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12339 eq14077
  have eq16383 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15520 eq20
    | exact resolve eq20 eq15520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15520
  have eq17793 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16383
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16383
    | exact resolve eq16383 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16383
  have eq18072 : False := by grind
  exact eq18072

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if m(X,Y) = X then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_x_pyy_pxy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq98 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op x x)
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq12
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
  have eq745 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq88 eq98
    | (have j0 := eq98 (M.op x y) x
       grind)
    | (have r₁ := eq98 (M.op x y) x
       have r₂ := eq88 (M.op x y)
       grind)
    | exact resolve eq98 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq746 : y ≠ y ∨ y = (k (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq77 eq98
    | (have j0 := eq98 y (M.op x y)
       grind)
    | (have r₁ := eq98 y (M.op x y)
       have r₂ := eq77 y
       grind)
    | exact resolve eq98 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq751 : y = (k (M.op x y) (M.op y y)) := by grind
  clear eq746
  have eq752 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by grind
  clear eq745
  have eq852 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq752 eq119
    | (have j0 := eq119 x (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq119 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y y))) ∨ (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | exact superpose eq751 eq119
    | (have j0 := eq119 (M.op x y) (M.op y y)
       grind)
    | exact resolve eq119 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq910 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq887 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq887
    | (have j0 := eq887 X0 X1
       grind)
    | exact resolve eq887 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq925 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y y))) ∨ (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | exact superpose eq20 eq854
    | exact resolve eq854 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq927 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq852
    | exact resolve eq852 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq945 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y y))) ∨ (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq925
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq925
    | exact resolve eq925 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq947 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq927
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq927
    | exact resolve eq927 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq955 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq945
       have i₂ := eq138 y
       grind)
    | exact superpose eq138 eq945
    | exact resolve eq945 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq957 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq947
       have i₂ := eq138 sF0
       grind)
    | exact superpose eq138 eq947
    | exact resolve eq947 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq961 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq955
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq955
    | exact resolve eq955 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq963 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq957
    | exact resolve eq957 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq966 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ (M.op x y)) (σ (M.op y y))) := by
    first
    | exact superpose eq20 eq961
    | exact resolve eq961 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq968 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq963
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq963
    | exact resolve eq963 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq971 : (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq966
       have i₂ := eq138 y
       grind)
    | exact superpose eq138 eq966
    | exact resolve eq966 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq974 : (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq968
       have i₂ := eq138 sF0
       grind)
    | exact superpose eq138 eq968
    | exact resolve eq968 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq979 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq971
       have i₂ := eq53 (σ y) (σ y) (σ y)
       grind)
    | (have i₁ := eq971
       have i₂ := eq53 x (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) x
       grind)
    | exact superpose eq53 eq971
    | exact resolve eq971 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq981 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq974
       have i₂ := eq53 (σ sF0) (σ sF0) (σ sF0)
       grind)
    | (have i₁ := eq974
       have i₂ := eq53 x (M.op (M.op (σ sF0) (σ sF0)) (M.op (σ sF0) (σ sF0))) x
       grind)
    | exact superpose eq53 eq974
    | exact resolve eq974 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq984 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq979
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq979
    | exact resolve eq979 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq986 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq981
    | exact resolve eq981 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq989 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq984
    | exact resolve eq984 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq991 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq986
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq986
    | exact resolve eq986 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq2077 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
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
  have eq2087 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq751 eq2077
    | exact resolve eq2077 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq2077
  have eq2102 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq2087
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2087
    | exact resolve eq2087 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2707 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq218
    | (have j0 := eq218 (M.op x y)
       grind)
    | exact resolve eq218 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq2716 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq752 eq2707
    | exact resolve eq2707 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707
  have eq2731 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq2716
    | exact resolve eq2716 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq29024 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq752
       have i₂ := eq910 x (M.op sF0 sF0)
       grind)
    | exact superpose eq910 eq752
    | (have j1 := eq910 x (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq752 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq29391 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq29024
       have i₂ := eq138 sF0
       grind)
    | exact superpose eq138 eq29024
    | exact resolve eq29024 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29024
  have eq29641 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq29391
    | exact resolve eq29391 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29391
  have eq29787 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq29641
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29641
    | exact resolve eq29641 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29641
  have eq29894 : (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29787
       have i₂ := eq138 sF0
       grind)
    | exact superpose eq138 eq29787
    | exact resolve eq29787 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29787
  have eq29954 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29894
       have i₂ := eq53 (σ sF0) (σ sF0) (σ sF0)
       grind)
    | (have i₁ := eq29894
       have i₂ := eq53 x (M.op (M.op (σ sF0) (σ sF0)) (M.op (σ sF0) (σ sF0))) x
       grind)
    | exact superpose eq53 eq29894
    | exact resolve eq29894 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29894
  have eq30009 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq29954
    | exact resolve eq29954 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29954
  have eq30054 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30009
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30009
    | exact resolve eq30009 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30009
  have eq72216 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq989 eq53
    | exact resolve eq53 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq73906 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq991 eq82
    | exact resolve eq82 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq73907 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq991 eq53
    | exact resolve eq53 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq78208 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq73907 eq81
    | exact resolve eq81 eq73907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq73907
  have eq78230 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq78208 eq53
    | exact resolve eq53 eq78208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78208
  have eq78248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq78230 eq72216
    | exact resolve eq72216 eq78230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78230
  have eq78266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq78248
    | exact resolve eq78248 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78248
  have eq78270 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq78266
       have r₂ := eq27
       grind)
    | exact resolve eq78266 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78266
  have eq78283 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq78270 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ y) (σ y))
       have r₂ := eq78270
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq78270
       grind)
    | exact resolve eq13 eq78270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78270
  have eq78297 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq78283
  have eq78307 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq78297
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq78297
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq78297
    | exact resolve eq78297 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78297
  have eq78308 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq78307
  have eq78317 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2102 eq78308
    | exact resolve eq78308 eq2102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78308
  have eq78318 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq78317
  have eq78328 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq78318 eq54
    | exact resolve eq54 eq78318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq78318
  have eq78723 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq73906 eq78328
    | exact resolve eq78328 eq73906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73906
  have eq78757 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq78723
  have eq92493 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq78757 eq78328
    | exact resolve eq78328 eq78757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78328 eq78757
  have eq92521 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq92493
  have eq96264 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq92521 eq13
    | (have r₁ := eq13 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq92521
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq92521
       grind)
    | exact resolve eq13 eq92521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92521
  have eq96278 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq96264
  have eq96294 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq96278
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq96278
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq96278
    | exact resolve eq96278 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96278
  have eq96295 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq96294
  have eq96304 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2731 eq96295
    | exact resolve eq96295 eq2731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2731 eq96295
  have eq96305 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq96304
  have eq96319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq96305 eq72216
    | exact resolve eq72216 eq96305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96305
  have eq96339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq96319
  have eq96356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq96339
    | exact resolve eq96339 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96339
  have eq96361 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq96356
       have r₂ := eq27
       grind)
    | exact resolve eq96356 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96356
  have eq96486 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq96361 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ y) (σ y))
       have r₂ := eq96361
       grind)
    | exact resolve eq13 eq96361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96361
  have eq96500 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq96486
  have eq96515 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq96500
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq96500
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq96500
    | exact resolve eq96500 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96500
  have eq96516 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq96515
  have eq96525 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2102 eq96516
    | exact resolve eq96516 eq2102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96516
  have eq96526 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq96525
  have eq96534 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq96526 eq39
    | exact resolve eq39 eq96526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq96526
  have eq96612 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq96534
    | exact resolve eq96534 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96534
  have eq96620 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq96612 eq38
    | exact resolve eq38 eq96612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq96612
  have eq96686 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq96620
    | exact resolve eq96620 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96620
  have eq96690 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96686 eq20
    | exact resolve eq20 eq96686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96691 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq96686 eq77
    | exact resolve eq77 eq96686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96776 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq96779 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96690
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq96690
    | exact resolve eq96690 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96690
  have eq97522 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96691 (M.op y x)
       have i₂ := eq96691 x
       grind)
    | exact superpose eq96691 eq96691
    | exact resolve eq96691 eq96691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96691
  have eq97544 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq97522
  have eq97579 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138 y
       have i₂ := eq97544
       grind)
    | exact superpose eq97544 eq138
    | exact resolve eq138 eq97544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97544
  have eq97622 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97579
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq97579
    | exact resolve eq97579 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97579
  have eq97942 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96779 eq97622
    | exact resolve eq97622 eq96779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97970 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97622 eq78
    | exact resolve eq78 eq97622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq97622
  have eq98008 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq97942
  have eq98131 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98008 eq258
    | exact resolve eq258 eq98008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq98008
  have eq98179 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq98131
    | exact resolve eq98131 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq98131
  have eq98261 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98179 eq752
    | exact resolve eq752 eq98179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq98179
  have eq98332 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq96686 eq98261
    | exact resolve eq98261 eq96686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96686 eq98261
  have eq98383 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq98332
       have r₂ := eq96776
       grind)
    | exact resolve eq98332 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98332
  have eq98508 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq98383
       grind)
    | exact superpose eq98383 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq98383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98383
  have eq98536 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq98508
       have r₂ := eq96776
       grind)
    | exact resolve eq98508 eq96776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96776 eq98508
  have eq98559 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98536
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98536
    | exact resolve eq98536 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98536
  have eq98560 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq98559
  have eq98580 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98560
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98560
    | exact resolve eq98560 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq98560
  have eq98655 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq98580
       grind)
    | exact superpose eq98580 eq77
    | exact resolve eq77 eq98580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq98580
  have eq98738 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98655 eq138
    | exact resolve eq138 eq98655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98655
  have eq98782 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq98738
    | exact resolve eq98738 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98738
  have eq98788 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98782
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq98782
    | exact resolve eq98782 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq98782
  have eq99341 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98788 eq30054
    | exact resolve eq30054 eq98788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30054 eq98788
  have eq99394 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq99341
  have eq99418 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq99394
    | exact resolve eq99394 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99394
  have eq99436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq99418
    | exact resolve eq99418 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99418
  have eq99438 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq99436
       have r₂ := eq27
       grind)
    | exact resolve eq99436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99436
  have eq99472 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99438 eq97970
    | exact resolve eq97970 eq99438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97970 eq99438
  have eq99477 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq99472
  have eq99481 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq99477
    | exact resolve eq99477 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99477
  have eq99494 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99481 eq27
    | exact resolve eq27 eq99481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99481
  have eq99546 : x = (M.op x y) := by
    first
    | (have r₁ := eq99494
       have r₂ := eq96779
       grind)
    | exact resolve eq99494 eq96779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96779 eq99494
  have eq99549 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq99546 eq20
    | exact resolve eq20 eq99546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq99558 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq99546 eq80
    | exact resolve eq80 eq99546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq99546
  have eq112897 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq99549
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq99549
    | exact resolve eq99549 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99549
  have eq113298 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq112897 eq22
    | exact resolve eq22 eq112897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq113299 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq112897 eq26
    | exact resolve eq26 eq112897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq112897
  have eq119136 : x = (M.op x x) := by
    first
    | (have i₁ := eq99558 (M.op x x)
       have i₂ := eq99558 x
       grind)
    | exact superpose eq99558 eq99558
    | exact resolve eq99558 eq99558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99558
  have eq119436 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq138 x
       have i₂ := eq119136
       grind)
    | exact superpose eq119136 eq138
    | exact resolve eq138 eq119136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq119136
  have eq119534 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq119436
       have i₂ := eq113298
       grind)
    | exact superpose eq113298 eq119436
    | exact resolve eq119436 eq113298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113298 eq119436
  have eq119790 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq119534 eq72216
    | exact resolve eq72216 eq119534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72216
  have eq119897 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq113299 eq119790
    | exact resolve eq119790 eq113299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119790
  have eq119926 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq119897
       have r₂ := eq27
       grind)
    | exact resolve eq119897 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119897
  have eq121120 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq119926 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ y) (σ y))
       have r₂ := eq119926
       grind)
    | exact resolve eq13 eq119926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119926
  have eq121134 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq121120
  have eq121143 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq121134
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq121134
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq121134
    | exact resolve eq121134 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq121134
  have eq121144 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by grind
  clear eq121143
  have eq121156 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2102 eq121144
    | exact resolve eq121144 eq2102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102 eq121144
  have eq121157 : (σ (M.op x y)) = (σ y) := by grind
  clear eq121156
  have eq124162 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq121157 eq113299
    | exact resolve eq113299 eq121157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113299 eq121157
  have eq124333 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq119534 eq124162
    | exact resolve eq124162 eq119534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119534 eq124162
  have eq124859 : False := by grind
  exact eq124859

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_pxy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  clear eq26
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
  have eq85 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq78 eq53
    | exact resolve eq53 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq81 eq53
    | exact resolve eq53 eq81
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
  have eq166 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq186 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq208 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq186
    | (have j0 := eq186 X0 X1
       grind)
    | exact resolve eq186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
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
  have eq224 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq166 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq166
    | exact resolve eq166 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
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
  have eq368 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 X0)) X0
       have i₂ := eq82 X0 X1 X2
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op X2 X2)) X2
       have r₂ := eq82 X2 X1 X2
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X2 X0)) X0
       have i₂ := eq82 X0 X1 X2
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq380 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
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
  have eq390 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
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
  have eq394 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq376 X0 X1 X2
       have j1 := eq368 X0 X1 X2
       grind)
    | (have r₁ := eq376 X0 X1 X2
       have r₂ := eq368 X0 X1 X2
       grind)
    | (have r₁ := eq376 X0 X0 X2
       have r₂ := eq368 X0 X0 X2
       grind)
    | exact resolve eq376 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq376
  have eq4627 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
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
  have eq4628 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4627 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627
  have eq4635 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq90 eq98
    | (have r₁ := eq98 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq90 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq98 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq4636 : (σ y) ≠ (σ y) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq78 eq98
    | (have r₁ := eq98 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq78 (σ y)
       grind)
    | exact resolve eq98 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq98
  have eq4637 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by grind
  clear eq4636
  have eq4638 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by grind
  clear eq4635
  have eq4657 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq4637 eq224
    | exact resolve eq224 eq4637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4660 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) (M.op (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq4657
       have i₂ := eq258 sF3
       grind)
    | exact superpose eq258 eq4657
    | exact resolve eq4657 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq4664 : y = (k (τ (M.op (σ x) (σ y))) (M.op y y)) := by
    first
    | exact superpose eq39 eq4660
    | exact resolve eq4660 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4660
  have eq4689 : (τ (M.op (σ x) (σ y))) = (k (τ (σ x)) (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq4638 eq224
    | exact resolve eq224 eq4638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq4638
  have eq4692 : (τ (M.op (σ x) (σ y))) = (k (τ (σ x)) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq4689
       have i₂ := eq258 sF4
       grind)
    | exact superpose eq258 eq4689
    | exact resolve eq4689 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4689
  have eq4697 : (τ (M.op (σ x) (σ y))) = (k x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq38 eq4692
    | exact resolve eq4692 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4692
  have eq4793 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4628 (M.op X0 X0) X1
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq4628
    | exact resolve eq4628 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4628
  have eq5041 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = (k (M.op X2 (M.op (τ X0) X1)) X1) ∨ (k X0 (σ X1)) = X0 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4793 X1 X1
       have i₂ := eq208 X0 X1
       grind)
    | (have i₁ := eq4793 (τ X0) X1
       have i₂ := eq208 X0 (τ X0)
       grind)
    | exact superpose eq208 eq4793
    | (have j1 := eq208 X0 X1
       grind)
    | exact resolve eq4793 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq4793
  have eq5161 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = (k (M.op X2 (M.op (τ X0) X1)) X1) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq5041 X0 X1 X2
       have j1 := eq394 (τ X0) X1 X2
       grind)
    | (have r₁ := eq5041 X0 X1 X2
       have r₂ := eq394 (τ X0) X1 X2
       grind)
    | exact resolve eq5041 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394 eq5041
  have eq180064 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5161 X0 X1 (M.op x (τ X0))
       have i₂ := eq53 x (τ X0) X1
       grind)
    | exact superpose eq53 eq5161
    | (have j0 := eq5161 X0 X1 x
       grind)
    | exact resolve eq5161 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5161
  have eq180073 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq38 eq180064
    | (have j0 := eq180064 (σ x) X0
       grind)
    | exact resolve eq180064 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180091 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq4664
       have i₂ := eq180064 sF4 (M.op y y)
       grind)
    | exact superpose eq180064 eq4664
    | (have j1 := eq180064 (M.op (σ x) (σ y)) (M.op y y)
       grind)
    | exact resolve eq4664 eq180064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4664 eq180064
  have eq180151 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) := by
    first
    | (have i₁ := eq180091
       have i₂ := eq138 y
       grind)
    | exact superpose eq138 eq180091
    | exact resolve eq180091 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq180091
  have eq180163 : ∀ X0 : G, (σ x) = (σ (k x X0)) ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq31 eq180073
    | (have j0 := eq180073 X0
       grind)
    | exact resolve eq180073 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq180073
  have eq180186 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) := by
    first
    | (have i₁ := eq180151
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq180151
    | exact resolve eq180151 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq180151
  have eq180198 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4637 eq180186
    | exact resolve eq180186 eq4637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4637 eq180186
  have eq180214 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq180198 eq53
    | exact resolve eq53 eq180198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180216 : ∀ X0 : G, y = (M.op (τ (M.op (σ x) (σ y))) (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq180198 eq54
    | exact resolve eq54 eq180198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180198
  have eq181469 : (σ x) = (σ (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq4697 eq180163
    | exact resolve eq180163 eq4697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4697
  have eq181882 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq181469
       have i₂ := eq11 sF4
       grind)
    | exact superpose eq11 eq181469
    | exact resolve eq181469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181469
  have eq183012 : ∀ X0 : G, x = (M.op (M.op X0 x) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq181882 eq53
    | exact resolve eq53 eq181882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq181882
  have eq183025 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq183012 eq180214
    | exact resolve eq180214 eq183012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180214 eq183012
  have eq183041 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq183025
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq183025
    | exact resolve eq183025 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183025
  have eq183053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq183041 eq11
    | exact resolve eq11 eq183041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183041
  have eq183413 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq183053
    | exact resolve eq183053 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183053
  have eq183417 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq183413
       have r₂ := eq27
       grind)
    | exact resolve eq183413 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183413
  have eq183418 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq183417 eq27
    | exact resolve eq27 eq183417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183420 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq183417 eq81
    | exact resolve eq81 eq183417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183426 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq183417 eq390
    | (have r₁ := eq390 X0
       have r₂ := eq183417
       grind)
    | exact resolve eq390 eq183417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq183437 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq183417
  have eq183438 : ∀ X0 : G, (σ y) = (k (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq183426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183426
  have eq186825 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq183420 eq183438
    | exact resolve eq183438 eq183420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183420 eq183438
  have eq186898 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq186825
  have eq186945 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64 eq186898
    | exact resolve eq186898 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq186898
  have eq187007 : (σ x) = (σ y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180163 y
       have i₂ := eq186945
       grind)
    | exact superpose eq186945 eq180163
    | (have j0 := eq180163 y
       grind)
    | exact resolve eq180163 eq186945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180163
  have eq187257 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq187007
       have r₂ := eq183437
       grind)
    | exact resolve eq187007 eq183437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183437 eq187007
  have eq187284 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq187257
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq187257
    | exact resolve eq187257 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187257
  have eq187544 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq186945
       have i₂ := eq187284
       grind)
    | exact superpose eq187284 eq186945
    | exact resolve eq186945 eq187284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186945 eq187284
  have eq187587 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq187544
  have eq187609 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq187587
    | exact resolve eq187587 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187587
  have eq187632 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq187609
       have r₂ := eq183418
       grind)
    | exact resolve eq187609 eq183418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183418 eq187609
  have eq187654 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq187632 eq27
    | exact resolve eq27 eq187632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq187656 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq187632 eq81
    | exact resolve eq81 eq187632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq187900 : ∀ X0 : G, (σ x) = (σ y) ∨ y = (M.op (τ (M.op (σ x) (σ y))) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq187632 eq180216
    | (have j0 := eq180216 X0
       grind)
    | exact resolve eq180216 eq187632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180216
  have eq188208 : ∀ X0 : G, y = (M.op (τ (σ x)) (M.op y X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq187632 eq187900
    | exact resolve eq187900 eq187632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187632 eq187900
  have eq188455 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq38 eq188208
    | exact resolve eq188208 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188208
  have eq188716 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq187656 eq187656
    | exact resolve eq187656 eq187656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187656
  have eq189867 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq188716 eq258
    | exact resolve eq258 eq188716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq188716
  have eq189981 : x = (M.op x x) := by
    first
    | exact superpose eq38 eq189867
    | exact resolve eq189867 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189867
  have eq190817 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq54 x x x
       have i₂ := eq189981
       grind)
    | exact superpose eq189981 eq54
    | exact resolve eq54 eq189981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq199903 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq190817 (M.op y x)
       have i₂ := eq188455 x
       grind)
    | exact superpose eq188455 eq190817
    | exact resolve eq190817 eq188455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188455 eq190817
  have eq199925 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq199903
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq199903
    | exact resolve eq199903 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199903
  have eq199929 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq199925 eq39
    | exact resolve eq39 eq199925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq199925
  have eq200140 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq199929
    | exact resolve eq199929 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq199929
  have eq200165 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq200140 eq20
    | exact resolve eq20 eq200140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200140
  have eq200443 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq200165
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq200165
    | exact resolve eq200165 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200165
  have eq200446 : x = y := by
    first
    | (have r₁ := eq200443
       have r₂ := eq187654
       grind)
    | exact resolve eq200443 eq187654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200443
  have eq200447 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq200446
       grind)
    | exact superpose eq200446 eq18
    | exact resolve eq18 eq200446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq200446
  have eq218295 : x = (M.op x y) := by
    first
    | (have i₁ := eq200447
       have i₂ := eq189981
       grind)
    | exact superpose eq189981 eq200447
    | exact resolve eq200447 eq189981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189981 eq200447
  have eq223466 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq218295 eq20
    | exact resolve eq20 eq218295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq218295
  have eq235096 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq223466
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq223466
    | exact resolve eq223466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq223466
  have eq235890 : False := by grind
  exact eq235890

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(Y,X) = m(Y,Y) then X else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_pyy_pxy_x_pyy_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X0 X3)) ≠ X0 ∨ (k (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X1 X2) X0) (M.op X0 X3)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) = (k X2 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq14 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq43
    | exact resolve eq43 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq74 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq70
    | exact resolve eq70 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq118 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq120 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq68 sF3
       grind)
    | exact superpose eq68 eq118
    | exact resolve eq118 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq68 y
       grind)
    | exact superpose eq68 eq120
    | exact resolve eq120 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq147 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq148 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq147
       have i₂ := eq68 sF1
       grind)
    | exact superpose eq68 eq147
    | exact resolve eq147 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq150 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq148
       have i₂ := eq68 sF0
       grind)
    | exact superpose eq68 eq148
    | exact resolve eq148 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq193 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq150 eq16
    | exact resolve eq16 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq150 eq36
    | exact resolve eq36 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq255 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (M.op X0 (M.op (M.op x y) (M.op x y))) ∨ (k X0 (M.op (M.op x y) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq12
    | (have j0 := eq12 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq12 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq255 eq14
    | exact resolve eq14 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq52 X2 X0 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq341 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = X0 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op x x)
       have i₂ := eq52 x x x
       grind)
    | exact superpose eq52 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq319 eq52
    | exact resolve eq52 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq34
    | exact resolve eq34 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq418 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq407 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq420 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq418 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq418
    | exact resolve eq418 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq442 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 X1 X2 X0
       have i₂ := eq52 X0 X0 X0
       grind)
    | exact superpose eq52 eq66
    | (have j0 := eq66 X0 X1 X2 X0
       grind)
    | (have r₁ := eq66 x X1 X2 x
       have r₂ := eq52 x x x
       grind)
    | exact resolve eq66 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq671 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X2) X0) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq663 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq787 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (σ X0) (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq52
    | exact resolve eq52 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 : G, (k (τ X0) (M.op (M.op x y) (M.op x y))) = (τ (k X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq150 eq411
    | exact resolve eq411 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq411 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq411
    | exact resolve eq411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq1027 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq20 eq442
    | (have j0 := eq442 (M.op x y) X0
       grind)
    | exact resolve eq442 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 x X0
       have i₂ := eq53 X0 x (M.op X0 x)
       grind)
    | exact superpose eq53 eq67
    | (have r₁ := eq67 X0 x X0
       have r₂ := eq53 X0 x (M.op X0 x)
       grind)
    | exact resolve eq67 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq67
  have eq1122 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1163 : (k (M.op x y) (k x x)) = (τ (k (σ (M.op x y)) (k (σ x) (σ x)))) := by
    first
    | exact superpose eq49 eq1027
    | exact resolve eq1027 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1027
  have eq1178 : (k (M.op x y) (k x x)) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq1163
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq1163
    | exact resolve eq1163 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1181 : (k (M.op x y) (M.op x x)) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq1178
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq1178
    | exact resolve eq1178 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1182 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1183 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1182 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq1182
    | (have j0 := eq1182 X0 X1
       grind)
    | exact resolve eq1182 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1184 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1183 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq1183
    | (have j0 := eq1183 X0 X1
       grind)
    | exact resolve eq1183 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1333 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (σ (k X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq50 eq1184
    | exact resolve eq1184 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1343 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq1184 X1 X0
       grind)
    | exact superpose eq1184 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq1184 X1 X0
       grind)
    | exact resolve eq12 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1361 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0)
       have i₂ := eq1184 X1 X0
       grind)
    | exact superpose eq1184 eq16
    | (have j1 := eq1184 X1 X0
       grind)
    | exact resolve eq16 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1382 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1343 X0 X1
       grind)
    | (have r₁ := eq1343 X0 X1
       have r₂ := eq75 X0
       grind)
    | exact resolve eq1343 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq1385 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (σ (k X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq150 eq1333
    | (have j0 := eq1333 X0
       grind)
    | exact resolve eq1333 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1405 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1382 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq1382
    | (have j0 := eq1382 X0 X1
       grind)
    | exact resolve eq1382 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq1406 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1405 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1409 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (σ (k X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq1385
    | (have j0 := eq1385 X0
       grind)
    | exact resolve eq1385 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1425 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1406 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq1406
    | (have j0 := eq1406 X0 X1
       grind)
    | exact resolve eq1406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq1428 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) ∨ (σ (M.op x y)) = (σ (k X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq150 eq1409
    | (have j0 := eq1409 X0
       grind)
    | exact resolve eq1409 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1443 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) ∨ (σ (M.op x y)) = (σ (k X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq1428
    | (have j0 := eq1428 X0
       grind)
    | exact resolve eq1428 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1452 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq1443
    | (have j0 := eq1443 X0
       grind)
    | exact resolve eq1443 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443
  have eq2537 : ∀ X0 X3 : G, (k (M.op X0 X3) (M.op X3 X3)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq671 X3 (M.op x X0) (M.op X0 x)
       have i₂ := eq52 x X0 x
       grind)
    | exact superpose eq52 eq671
    | exact resolve eq671 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq2794 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)))) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq442 X0 (M.op (M.op (σ X0) X1) (M.op (σ X0) X1))
       have i₂ := eq1122 (σ X0) X1
       grind)
    | exact superpose eq1122 eq442
    | exact resolve eq442 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq1122
  have eq6101 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ y = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq351 eq264
    | (have j0 := eq264 y
       grind)
    | (have r₁ := eq264 y
       have r₂ := eq351 (M.op x y)
       grind)
    | exact resolve eq264 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq351
  have eq6104 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ y = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq6101
  have eq7056 : x ≠ x ∨ x = (M.op (M.op x y) (M.op x x)) ∨ (M.op x y) = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq330 eq341
    | (have j0 := eq341 x (M.op x y)
       grind)
    | (have r₁ := eq341 x (M.op x y)
       have r₂ := eq330 x
       grind)
    | exact resolve eq341 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq7065 : (M.op x y) = (k (M.op x y) (M.op x x)) ∨ x = (M.op (M.op x y) (M.op x x)) := by grind
  clear eq7056
  have eq12523 : ∀ X0 : G, (τ (σ (M.op x y))) = (k X0 (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1452 eq16
    | (have j1 := eq1452 X0
       grind)
    | exact resolve eq16 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq12555 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k X0 (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq30 eq12523
    | (have j0 := eq12523 X0
       grind)
    | exact resolve eq12523 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12523
  have eq13987 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq1425 X0 X1
       grind)
    | exact superpose eq1425 eq13
    | (have j1 := eq1425 X0 X1
       grind)
    | exact resolve eq13 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq14031 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq13987 X0 X1
       grind)
    | (have r₁ := eq13987 X0 X1
       have r₂ := eq75 X0
       grind)
    | exact resolve eq13987 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13987
  have eq14107 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14031 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq14031
    | (have j0 := eq14031 X0 X1
       grind)
    | exact resolve eq14031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14031
  have eq14108 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq14107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14107
  have eq22603 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq1361 X0 X1
       grind)
    | exact superpose eq1361 eq13
    | (have j1 := eq1361 X0 X1
       grind)
    | exact resolve eq13 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq22650 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq22603 X0 X1
       grind)
    | (have r₁ := eq22603 X0 X1
       have r₂ := eq75 X0
       grind)
    | exact resolve eq22603 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq22603
  have eq22746 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22650 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq22650
    | (have j0 := eq22650 X0 X1
       grind)
    | exact resolve eq22650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22650
  have eq22747 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq22746 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22746
  have eq34959 : y = (k y (M.op (M.op x y) (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6104 eq319
    | exact resolve eq319 eq6104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6104
  have eq35658 : (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq34959 eq195
    | exact resolve eq195 eq34959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq34959
  have eq35693 : (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq35658
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35658
    | exact resolve eq35658 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35658
  have eq67817 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14108 (τ X0) (τ X1)
       have i₂ := eq814 X0 X1
       grind)
    | exact superpose eq814 eq14108
    | exact resolve eq14108 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq14108
  have eq68620 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq67817 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq67817
    | (have j0 := eq67817 X0 X1
       grind)
    | exact resolve eq67817 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67817
  have eq68809 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq68620 X0 X1
       have i₂ := eq420 X1
       grind)
    | exact superpose eq420 eq68620
    | (have j0 := eq68620 X0 X1
       grind)
    | exact resolve eq68620 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68620
  have eq68903 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68809 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq68809
    | (have j0 := eq68809 X0 X1
       grind)
    | exact resolve eq68809 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68809
  have eq68928 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68903 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq68903
    | (have j0 := eq68903 X0 X1
       grind)
    | exact resolve eq68903 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68903
  have eq76794 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68928 X1 (M.op X0 X0)
       have i₂ := eq52 X0 X0 X0
       grind)
    | exact superpose eq52 eq68928
    | (have j0 := eq68928 X1 (M.op X0 X0)
       grind)
    | exact resolve eq68928 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68928
  have eq112347 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq76794 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76794
  have eq378504 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (M.op (σ (τ X0)) (σ X1)))) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq420 X0
       have i₂ := eq22747 (τ X0) X1
       grind)
    | exact superpose eq22747 eq420
    | (have j1 := eq22747 (τ X0) X1
       grind)
    | exact resolve eq420 eq22747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22747
  have eq378875 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq378504 X0 X1
       have i₂ := eq15 (M.op (σ (τ X0)) (σ X1))
       grind)
    | exact superpose eq15 eq378504
    | (have j0 := eq378504 X0 X1
       grind)
    | exact resolve eq378504 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378504
  have eq379158 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq378875 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq378875
    | (have j0 := eq378875 X0 X1
       grind)
    | exact resolve eq378875 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378875
  have eq379328 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq379158 X0 X1
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq379158
    | (have j0 := eq379158 X0 X1
       grind)
    | exact resolve eq379158 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq379158
  have eq379410 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq379328 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq379328
    | (have j0 := eq379328 X0 X1
       grind)
    | exact resolve eq379328 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq379328
  have eq504281 : ∀ X0 : G, (τ (σ (M.op x y))) = (k X0 (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (M.op x y) = (k X0 (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq12555 eq2794
    | (have j1 := eq12555 X0
       grind)
    | exact resolve eq2794 eq12555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794 eq12555
  have eq504429 : ∀ X0 : G, (τ (σ (M.op x y))) = (k X0 (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (k X0 (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq193 eq504281
    | (have j0 := eq504281 X0
       grind)
    | exact resolve eq504281 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504281
  have eq504467 : ∀ X0 : G, (M.op x y) = (k X0 (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (k X0 (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq30 eq504429
    | (have j0 := eq504429 X0
       grind)
    | exact resolve eq504429 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504429
  have eq504468 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) ∨ (M.op x y) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq504467 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504467
  have eq505096 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X1 (σ (M.op x y))) (σ X0)) ∨ (M.op x y) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq504468 eq322
    | (have j1 := eq504468 X0
       grind)
    | exact resolve eq322 eq504468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq504468
  have eq507749 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X1 (σ (M.op x y))) X0) ∨ (M.op x y) = (k (τ X0) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq505096 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq505096
    | (have j0 := eq505096 (τ X0) X1
       grind)
    | exact resolve eq505096 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505096
  have eq508423 : ∀ X0 X1 : G, (M.op x y) = (τ (k X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (M.op X1 (σ (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq813 eq507749
    | (have j0 := eq507749 X0 X1
       grind)
    | exact resolve eq507749 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq507749
  have eq510646 : ∀ X0 : G, (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq35693 eq508423
    | (have j0 := eq508423 (σ y) X0
       grind)
    | exact resolve eq508423 eq35693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35693 eq508423
  have eq510997 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq29 eq510646
    | (have j0 := eq510646 X0
       grind)
    | exact resolve eq510646 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq510646
  have eq719263 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq379410 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq379410
    | exact resolve eq379410 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379410
  have eq722440 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq719263 X0 (M.op x x)
       have i₂ := eq52 x x x
       grind)
    | exact superpose eq52 eq719263
    | exact resolve eq719263 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719263
  have eq734735 : (τ (σ x)) = (k (M.op x y) (M.op x x)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1181
       have i₂ := eq722440 sF2 sF1
       grind)
    | exact superpose eq722440 eq1181
    | (have j1 := eq722440 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq1181 eq722440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq722440
  have eq735115 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq28 eq734735
    | exact resolve eq734735 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq734735
  have eq760025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq735115 eq510997
    | exact resolve eq510997 eq735115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq26 eq760025
    | exact resolve eq760025 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760025
  have eq760177 : x = (k (M.op x y) (M.op x x)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq760158
       have r₂ := eq27
       grind)
    | exact resolve eq760158 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760158
  have eq760524 : x = (M.op (M.op x y) (M.op x x)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7065 eq760177
    | exact resolve eq760177 eq7065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760177
  have eq771795 : (M.op x y) = (M.op x x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq760524 eq268
    | exact resolve eq268 eq760524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760524
  have eq771951 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq771795
       grind)
    | exact superpose eq771795 eq74
    | exact resolve eq74 eq771795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771795
  have eq772415 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq771951
    | exact resolve eq771951 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771951
  have eq774459 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq772415 eq2537
    | exact resolve eq2537 eq772415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2537 eq772415
  have eq774513 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq774459
       have i₂ := eq68 sF1
       grind)
    | exact superpose eq68 eq774459
    | exact resolve eq774459 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq774459
  have eq791313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq774513 eq510997
    | exact resolve eq510997 eq774513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774513
  have eq791547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq791313
  have eq791618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq791547
    | exact resolve eq791547 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791547
  have eq791706 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq791618
       have r₂ := eq27
       grind)
    | exact resolve eq791618 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791618
  have eq791883 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq791706 eq787
    | exact resolve eq787 eq791706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq791706
  have eq792164 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq791883 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq791883
    | (have j0 := eq791883 X0
       grind)
    | exact resolve eq791883 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791883
  have eq792284 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq792164
    | (have j0 := eq792164 X0
       grind)
    | exact resolve eq792164 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792164
  have eq811274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq735115 eq792284
    | exact resolve eq792284 eq735115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | (have j1 := eq112347 (M.op x y) x
       grind)
    | (have r₁ := eq811274
       have r₂ := eq112347 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq811274
       have r₂ := eq112347 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq811274
       have r₂ := eq112347 y (M.op x y)
       grind)
    | exact resolve eq811274 eq112347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811274
  have eq811462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq26 eq811460
    | exact resolve eq811460 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811460
  have eq811463 : x = (k (M.op x y) (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq811462
       have r₂ := eq27
       grind)
    | exact resolve eq811462 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811462
  have eq811466 : x = (M.op (M.op x y) (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7065 eq811463
    | exact resolve eq811463 eq7065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811463
  have eq821293 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq811466 eq268
    | exact resolve eq268 eq811466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811466
  have eq821593 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq330 x
       have i₂ := eq821293
       grind)
    | exact superpose eq821293 eq330
    | exact resolve eq330 eq821293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821293
  have eq822539 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq821593 eq150
    | exact resolve eq150 eq821593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821593
  have eq823052 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq822539
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq822539
    | exact resolve eq822539 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822539
  have eq829016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq823052 eq792284
    | exact resolve eq792284 eq823052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792284 eq823052
  have eq829246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq829016
  have eq829319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq829246
    | exact resolve eq829246 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829246
  have eq829385 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq829319
       have r₂ := eq27
       grind)
    | exact resolve eq829319 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829319
  have eq829401 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq829385 eq20
    | exact resolve eq20 eq829385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829415 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq829385 eq150
    | exact resolve eq150 eq829385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq829459 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq829385 eq319
    | exact resolve eq319 eq829385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq829385
  have eq830620 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq829415
       have i₂ := eq122
       grind)
    | exact superpose eq122 eq829415
    | exact resolve eq829415 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829415
  have eq830633 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq829401
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq829401
    | exact resolve eq829401 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829401
  have eq834727 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq829459 (M.op y x)
       have i₂ := eq829459 x
       grind)
    | exact superpose eq829459 eq829459
    | exact resolve eq829459 eq829459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829459
  have eq834861 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq834727
  have eq835046 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq834861
       grind)
    | exact superpose eq834861 eq122
    | exact resolve eq122 eq834861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq834861
  have eq835526 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq835046
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq835046
    | exact resolve eq835046 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835046
  have eq837732 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq830633 eq835526
    | exact resolve eq835526 eq830633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830633
  have eq838070 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq837732
  have eq844015 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq838070 eq193
    | exact resolve eq193 eq838070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq838070
  have eq844455 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq844015
    | exact resolve eq844015 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq844015
  have eq849815 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq830620 eq835526
    | exact resolve eq835526 eq830620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830620 eq835526
  have eq850076 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq849815
  have eq850485 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq850076 eq52
    | exact resolve eq52 eq850076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq850076
  have eq905892 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq735115 eq850485
    | exact resolve eq850485 eq735115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735115 eq850485
  have eq906123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | (have j1 := eq112347 (M.op x y) x
       grind)
    | (have r₁ := eq905892
       have r₂ := eq112347 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq905892
       have r₂ := eq112347 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq905892
       have r₂ := eq112347 x (M.op x y)
       grind)
    | exact resolve eq905892 eq112347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112347 eq905892
  have eq906126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq26 eq906123
    | exact resolve eq906123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906123
  have eq906128 : x = (k (M.op x y) (M.op x x)) := by
    first
    | (have r₁ := eq906126
       have r₂ := eq27
       grind)
    | exact resolve eq906126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906126
  have eq906134 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7065 eq906128
    | exact resolve eq906128 eq7065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7065 eq906128
  have eq986695 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq906134 eq268
    | exact resolve eq268 eq906134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq906134
  have eq988044 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq330 x
       have i₂ := eq986695
       grind)
    | exact superpose eq986695 eq330
    | exact resolve eq330 eq986695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986695
  have eq989403 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq988044 eq844455
    | exact resolve eq844455 eq988044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844455 eq988044
  have eq989716 : x = (M.op x y) := by grind
  clear eq989403
  have eq990019 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq989716 eq20
    | exact resolve eq20 eq989716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq990065 : x = (M.op (M.op x x) x) := by
    first
    | exact superpose eq989716 eq255
    | exact resolve eq255 eq989716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq991283 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq990019
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq990019
    | exact resolve eq990019 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990019
  have eq993432 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq991283 eq26
    | exact resolve eq26 eq991283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq994520 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq330 (M.op x x)
       have i₂ := eq990065
       grind)
    | exact superpose eq990065 eq330
    | exact resolve eq330 eq990065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq990065
  have eq994678 : x = (M.op x x) := by
    first
    | exact superpose eq989716 eq994520
    | exact resolve eq994520 eq989716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994520
  have eq994722 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq994678
       grind)
    | exact superpose eq994678 eq74
    | exact resolve eq74 eq994678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq995305 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq991283 eq994722
    | exact resolve eq994722 eq991283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994722
  have eq995483 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq995305
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq995305
    | exact resolve eq995305 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995305
  have eq995593 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq991283 eq995483
    | exact resolve eq995483 eq991283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995483
  have eq995871 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq995593 eq510997
    | exact resolve eq510997 eq995593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510997
  have eq996252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq993432 eq995871
    | exact resolve eq995871 eq993432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995871
  have eq996425 : y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq996252
       have r₂ := eq27
       grind)
    | exact resolve eq996252 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996252
  have eq996519 : x = y ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq989716 eq996425
    | exact resolve eq996425 eq989716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996425
  have eq996585 : y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq989716 eq996519
    | exact resolve eq996519 eq989716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989716 eq996519
  have eq996613 : x = y ∨ x = y := by
    first
    | (have i₁ := eq996585
       have i₂ := eq994678
       grind)
    | exact superpose eq994678 eq996585
    | exact resolve eq996585 eq994678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994678 eq996585
  have eq996614 : x = y := by grind
  clear eq996613
  have eq996634 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq996614
       grind)
    | exact superpose eq996614 eq24
    | exact resolve eq24 eq996614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq996614
  have eq998084 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq996634
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq996634
    | exact resolve eq996634 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq996634
  have eq998619 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq991283 eq998084
    | exact resolve eq998084 eq991283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991283 eq998084
  have eq1000885 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq998619 eq993432
    | exact resolve eq993432 eq998619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993432 eq998619
  have eq1000886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq995593 eq1000885
    | exact resolve eq1000885 eq995593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995593 eq1000885
  have eq1001255 : False := by grind
  exact eq1001255

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyy_x_pxy_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X1) := by
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
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq24 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq28 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq29 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq32 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq28 X2 X0 x
       grind)
    | exact superpose eq28 eq28
    | exact resolve eq28 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 X2)) ≠ X0 ∨ (σ X0) = (k (σ (M.op X1 X0)) (σ (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (M.op X0 x) (M.op x x)
       have i₂ := eq28 X0 x x
       grind)
    | exact superpose eq28 eq59
    | exact resolve eq59 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq59 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq10
    | exact resolve eq10 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq24 (σ X0) (σ X0)
       grind)
    | exact superpose eq24 eq92
    | exact resolve eq92 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq96 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq95 (σ X0)
       grind)
    | exact superpose eq95 eq83
    | exact resolve eq83 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq97 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0 X0
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq24
    | exact resolve eq24 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq100 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq95 (τ X0)
       grind)
    | exact superpose eq95 eq97
    | exact resolve eq97 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq97
  have eq385 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X0) = (k (σ (M.op X1 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1 X0
       have i₂ := eq28 X0 X0 X0
       grind)
    | exact superpose eq28 eq80
    | (have j0 := eq80 X0 X1 X0
       grind)
    | (have r₁ := eq80 x X1 x
       have r₂ := eq28 x x x
       grind)
    | exact resolve eq80 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq386 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X1 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq385 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq387 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X1 X0)) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq386
    | exact resolve eq386 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq400 : ∀ X0 X1 : G, (k (σ (M.op X1 (τ X0))) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq387 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq387
    | exact resolve eq387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq474 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op X1 (τ X0))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (σ (M.op X1 (τ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ (M.op X1 (τ X0))) (M.op X0 X0)
       have i₂ := eq400 X0 X1
       grind)
    | exact superpose eq400 eq14
    | (have j0 := eq14 (σ (M.op X1 (τ X0))) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq481 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = X0 ∨ (σ (M.op X1 (τ X0))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (σ (M.op X1 (τ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq474 X0 X1
       have i₂ := eq28 X0 X0 X0
       grind)
    | (have i₁ := eq474 X0 X1
       have i₂ := eq28 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq28 eq474
    | (have j0 := eq474 X0 X1
       grind)
    | exact resolve eq474 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq482 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (σ (M.op X1 (τ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq481 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq490 : ∀ X0 X1 : G, (M.op (σ (M.op X1 (τ X0))) (M.op X0 X0)) = X0 ∨ (σ (M.op X1 (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq482 X0 X1
       have i₂ := eq28 X0 X0 X0
       grind)
    | (have i₁ := eq482 X0 X1
       have i₂ := eq28 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq28 eq482
    | (have j0 := eq482 X0 X1
       grind)
    | exact resolve eq482 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq1192 : ∀ X0 X1 X2 : G, (σ (M.op X1 (τ X0))) = X0 ∨ (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (σ (M.op X1 (τ X0))) (M.op X0 X0) x
       have i₂ := eq490 X0 X1
       grind)
    | exact superpose eq490 eq29
    | (have j1 := eq490 X0 X1
       grind)
    | exact resolve eq29 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1285 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq1192 X0 X1 X2
       grind)
    | exact superpose eq1192 eq10
    | (have j1 := eq1192 X0 X1 X2
       grind)
    | exact resolve eq10 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1366 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1285 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1285
    | exact resolve eq1285 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1418 : ∀ X0 X1 X3 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (M.op (σ (M.op X0 X1)) X3)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1366 (M.op x x) (M.op X0 x) x
       have i₂ := eq28 X0 x x
       grind)
    | exact superpose eq28 eq1366
    | exact resolve eq1366 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2260 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1418 X1 X0 (M.op (σ X0) x)
       have i₂ := eq1366 X0 X1 x
       grind)
    | exact superpose eq1366 eq1418
    | (have j0 := eq1418 X1 X0 x
       have j1 := eq1366 X0 X1 x
       grind)
    | exact resolve eq1418 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366
  have eq4421 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2260 y x
       grind)
    | exact superpose eq2260 eq16
    | (have j1 := eq2260 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq2260 y x
       grind)
    | exact resolve eq16 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq4508 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4421
  have eq4558 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x y
       have i₂ := eq4508
       grind)
    | exact superpose eq4508 eq28
    | exact resolve eq28 eq4508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4560 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq29 x y x
       have i₂ := eq4508
       grind)
    | exact superpose eq4508 eq29
    | exact resolve eq29 eq4508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq4561 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq32 y x x
       have i₂ := eq4508
       grind)
    | exact superpose eq4508 eq32
    | exact resolve eq32 eq4508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4508
  have eq4673 : ∀ X0 X1 : G, y = (M.op x (M.op y X0)) ∨ y = (M.op x (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 x y X0
       have i₂ := eq4560 X1
       grind)
    | exact superpose eq4560 eq28
    | (have j1 := eq4560 X0
       grind)
    | exact resolve eq28 eq4560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4560
  have eq4699 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4561 (M.op x y)
       have i₂ := eq4561 x
       grind)
    | exact superpose eq4561 eq4561
    | exact resolve eq4561 eq4561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4561
  have eq4727 : x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq4699
  have eq4901 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x y
       have i₂ := eq4727
       grind)
    | exact superpose eq4727 eq28
    | exact resolve eq28 eq4727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4727
  have eq4944 : x = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4901 (M.op x x)
       have i₂ := eq4901 x
       grind)
    | exact superpose eq4901 eq4901
    | exact resolve eq4901 eq4901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4901
  have eq4974 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq4944
  have eq4981 : x = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq96 y
       have i₂ := eq4974
       grind)
    | exact superpose eq4974 eq96
    | exact resolve eq96 eq4974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4974
  have eq5378 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4558 x
       have i₂ := eq4981
       grind)
    | exact superpose eq4981 eq4558
    | exact resolve eq4558 eq4981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558
  have eq5383 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq96 x
       have i₂ := eq4981
       grind)
    | exact superpose eq4981 eq96
    | exact resolve eq96 eq4981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4981
  have eq5432 : x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5378
  have eq5502 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5432
       grind)
    | exact superpose eq5432 eq16
    | exact resolve eq16 eq5432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5432
  have eq5815 : ∀ X0 : G, y ≠ y ∨ y = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have j0 := eq4673 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673
  have eq5816 : ∀ X0 : G, y = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have j0 := eq5815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5815
  have eq5845 : ∀ X1 : G, x = y ∨ (σ y) = (M.op (σ x) (M.op (σ y) X1)) := by
    intro X1
    first
    | (have i₁ := eq1418 x (M.op y x) x
       have i₂ := eq5816 x
       grind)
    | exact superpose eq5816 eq1418
    | exact resolve eq1418 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq6687 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq5845 x
       grind)
    | exact superpose eq5845 eq16
    | (have j1 := eq5845 X0
       grind)
    | exact resolve eq16 eq5845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5845
  have eq6717 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq6687 X0
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq6687
    | (have j0 := eq6687 X0
       grind)
    | (have r₁ := eq6687 X0
       have r₂ := eq96 x
       grind)
    | exact resolve eq6687 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq6687
  have eq6718 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq6717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6717
  have eq6733 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ x) (M.op (σ y) x)
       have i₂ := eq6718 x
       grind)
    | exact superpose eq6718 eq28
    | exact resolve eq28 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq8827 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6733 (σ x)
       have i₂ := eq5383
       grind)
    | exact superpose eq5383 eq6733
    | exact resolve eq6733 eq5383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5383 eq6733
  have eq9583 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5502
       have i₂ := eq8827
       grind)
    | exact superpose eq8827 eq5502
    | (have r₁ := eq5502
       have r₂ := eq8827
       grind)
    | exact resolve eq5502 eq8827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5502 eq8827
  have eq9626 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq9583
  have eq9627 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq9626
  have eq9665 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6718 (σ y)
       have i₂ := eq9627
       grind)
    | exact superpose eq9627 eq6718
    | exact resolve eq6718 eq9627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6718
  have eq9682 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq100 (σ y)
       have i₂ := eq9627
       grind)
    | exact superpose eq9627 eq100
    | exact resolve eq100 eq9627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq9627
  have eq9749 : y = (M.op y y) := by
    first
    | (have i₁ := eq9682
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq9682
    | exact resolve eq9682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9682
  have eq9766 : y = (M.op x y) := by
    first
    | (have i₁ := eq5816 y
       have i₂ := eq9749
       grind)
    | exact superpose eq9749 eq5816
    | exact resolve eq5816 eq9749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5816 eq9749
  have eq10092 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9766
       grind)
    | exact superpose eq9766 eq16
    | exact resolve eq16 eq9766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9766
  have eq10377 : False := by grind
  exact eq10377

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
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

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_pxy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op a b :=
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

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq89 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq81 eq54
    | exact resolve eq54 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op x x)
       have i₂ := eq54 x x x
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
  have eq120 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq497 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 (M.op X1 X0)
       have i₂ := eq54 X1 X0 X0
       grind)
    | exact superpose eq54 eq99
    | (have j0 := eq99 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq99 x (M.op X0 x)
       have r₂ := eq54 X0 x x
       grind)
    | exact resolve eq99 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq89 eq99
    | (have j0 := eq99 (M.op x y) x
       grind)
    | (have r₁ := eq99 (M.op x y) x
       have r₂ := eq89 (M.op x y)
       grind)
    | exact resolve eq99 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq500 : y ≠ y ∨ y = (k (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq78 eq99
    | (have j0 := eq99 y (M.op x y)
       grind)
    | (have r₁ := eq99 y (M.op x y)
       have r₂ := eq78 y
       grind)
    | exact resolve eq99 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq505 : y = (k (M.op x y) (M.op y y)) := by grind
  clear eq500
  have eq506 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by grind
  clear eq499
  have eq507 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq497 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq521 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ (M.op x y)) (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | exact superpose eq505 eq120
    | (have j0 := eq120 (M.op x y) (M.op y y)
       grind)
    | exact resolve eq120 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq526 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ (M.op x y)) (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | exact superpose eq21 eq521
    | exact resolve eq521 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq528 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ (M.op x y)) (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq526
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq526
    | exact resolve eq526 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq529 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq528
       have i₂ := eq137 y
       grind)
    | exact superpose eq137 eq528
    | exact resolve eq528 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq530 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq529
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq529
    | exact resolve eq529 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq531 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | exact superpose eq21 eq530
    | exact resolve eq530 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq532 : (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq531
       have i₂ := eq137 y
       grind)
    | exact superpose eq137 eq531
    | exact resolve eq531 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq533 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq532
       have i₂ := eq54 (σ y) (σ y) (σ y)
       grind)
    | (have i₁ := eq532
       have i₂ := eq54 x (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) x
       grind)
    | exact superpose eq54 eq532
    | exact resolve eq532 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq534 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq533
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq533
    | exact resolve eq533 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq535 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq534
    | exact resolve eq534 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq548 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq506 eq120
    | (have j0 := eq120 x (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq120 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq553 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq21 eq548
    | exact resolve eq548 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq555 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq553
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq553
    | exact resolve eq553 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq556 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq555
       have i₂ := eq137 sF0
       grind)
    | exact superpose eq137 eq555
    | exact resolve eq555 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq557 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq21 eq556
    | exact resolve eq556 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq558 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq557
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq557
    | exact resolve eq557 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq559 : (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq558
       have i₂ := eq137 sF0
       grind)
    | exact superpose eq137 eq558
    | exact resolve eq558 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq560 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq559
       have i₂ := eq54 (σ sF0) (σ sF0) (σ sF0)
       grind)
    | (have i₁ := eq559
       have i₂ := eq54 x (M.op (M.op (σ sF0) (σ sF0)) (M.op (σ sF0) (σ sF0))) x
       grind)
    | exact superpose eq54 eq559
    | exact resolve eq559 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq561 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq560
    | exact resolve eq560 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq562 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq561
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq561
    | exact resolve eq561 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq7865 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq535 eq54
    | exact resolve eq54 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq11541 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq562 eq54
    | exact resolve eq54 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq12789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11541 eq7865
    | exact resolve eq7865 eq11541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11541
  have eq12803 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq12789
    | exact resolve eq12789 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12789
  have eq12805 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq12803
       have r₂ := eq28
       grind)
    | exact resolve eq12803 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12803
  have eq12836 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12805 eq507
    | exact resolve eq507 eq12805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12805
  have eq12842 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12836
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq12836
    | exact resolve eq12836 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12836
  have eq12893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12842 eq562
    | exact resolve eq562 eq12842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12925 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq12842
  have eq12928 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq12893
  have eq12946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq12928
       have r₂ := eq12925
       grind)
    | exact resolve eq12928 eq12925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12925 eq12928
  have eq12950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq12946
    | exact resolve eq12946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12946
  have eq12951 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq12950
       have r₂ := eq28
       grind)
    | exact resolve eq12950 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12950
  have eq12962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12951 eq7865
    | exact resolve eq7865 eq12951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12981 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12951 eq507
    | exact resolve eq507 eq12951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq12962
  have eq12989 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12981
       have i₂ := eq100 sF2
       grind)
    | exact superpose eq100 eq12981
    | exact resolve eq12981 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12981
  have eq12997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq12985
    | exact resolve eq12985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12985
  have eq13009 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq12997
       have r₂ := eq28
       grind)
    | exact resolve eq12997 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12997
  have eq13773 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13009 eq507
    | exact resolve eq507 eq13009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13009
  have eq13779 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13773
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq13773
    | exact resolve eq13773 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13773
  have eq13883 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13779 eq12951
    | exact resolve eq12951 eq13779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12951 eq13779
  have eq13908 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13883
  have eq13931 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13908 eq27
    | exact resolve eq27 eq13908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13935 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13908 eq40
    | exact resolve eq40 eq13908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13908
  have eq13995 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq39 eq13935
    | exact resolve eq13935 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13935
  have eq14004 : y = (τ (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13995 eq40
    | exact resolve eq40 eq13995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13995
  have eq14052 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq14004
    | exact resolve eq14004 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14004
  have eq14060 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq14052 eq39
    | exact resolve eq39 eq14052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14052
  have eq14106 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq14060
    | exact resolve eq14060 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14060
  have eq14283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13931 eq12989
    | exact resolve eq12989 eq13931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12989 eq13931
  have eq14309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq14283
  have eq14318 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq14309
       have r₂ := eq28
       grind)
    | exact resolve eq14309 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14309
  have eq15389 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14318 eq40
    | exact resolve eq40 eq14318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq14318
  have eq15437 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq15389
    | exact resolve eq15389 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15389
  have eq15445 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15437 eq39
    | exact resolve eq39 eq15437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15437
  have eq15491 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq15445
    | exact resolve eq15445 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15445
  have eq15495 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15491 eq21
    | exact resolve eq21 eq15491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15496 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15491 eq78
    | exact resolve eq78 eq15491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15522 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq15491
  have eq15523 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15495
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15495
    | exact resolve eq15495 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15495
  have eq16129 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15496 (M.op y x)
       have i₂ := eq15496 x
       grind)
    | exact superpose eq15496 eq15496
    | exact resolve eq15496 eq15496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15496
  have eq16144 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq16129
  have eq16170 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq137 y
       have i₂ := eq16144
       grind)
    | exact superpose eq16144 eq137
    | exact resolve eq137 eq16144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16144
  have eq16195 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16170
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16170
    | exact resolve eq16170 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16170
  have eq16224 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15523 eq16195
    | exact resolve eq16195 eq15523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16195
  have eq16281 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq16224
  have eq16381 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16281 eq257
    | exact resolve eq257 eq16281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq16281
  have eq16412 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq16381
    | exact resolve eq16381 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16381
  have eq16483 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16412 eq506
    | exact resolve eq506 eq16412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq16412
  have eq16524 : y = (k x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14106 eq16483
    | exact resolve eq16483 eq14106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14106 eq16483
  have eq16541 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq16524
  have eq16550 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16541
       have r₂ := eq15522
       grind)
    | exact resolve eq16541 eq15522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16541
  have eq17521 : x = y ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq16550
       grind)
    | exact superpose eq16550 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq16550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16550
  have eq17522 : x = y ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq17521
  have eq17526 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17522
       have r₂ := eq15522
       grind)
    | exact resolve eq17522 eq15522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15522 eq17522
  have eq17541 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17526
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17526
    | exact resolve eq17526 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17526
  have eq17579 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq17541
       grind)
    | exact superpose eq17541 eq78
    | exact resolve eq78 eq17541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq17541
  have eq17629 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17579 eq137
    | exact resolve eq137 eq17579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17579
  have eq17656 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq17629
    | exact resolve eq17629 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17629
  have eq17659 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17656
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17656
    | exact resolve eq17656 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17656
  have eq17809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17659 eq562
    | exact resolve eq562 eq17659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq17659
  have eq17869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17809
    | exact resolve eq17809 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17809
  have eq17873 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17869
       have r₂ := eq28
       grind)
    | exact resolve eq17869 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17869
  have eq19856 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17873 eq15523
    | exact resolve eq15523 eq17873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15523 eq17873
  have eq19865 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq19856
  have eq19883 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19865 eq39
    | exact resolve eq39 eq19865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq19865
  have eq19931 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq19883
    | exact resolve eq19883 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq19883
  have eq19932 : x = (M.op x y) := by grind
  clear eq19931
  have eq19937 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19932 eq21
    | exact resolve eq21 eq19932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq19946 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq19932 eq81
    | exact resolve eq81 eq19932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq19932
  have eq21797 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19937
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19937
    | exact resolve eq19937 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19937
  have eq21903 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21797 eq23
    | exact resolve eq23 eq21797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq21904 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21797 eq27
    | exact resolve eq27 eq21797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21797
  have eq23488 : x = (M.op x x) := by
    first
    | (have i₁ := eq19946 (M.op x x)
       have i₂ := eq19946 x
       grind)
    | exact superpose eq19946 eq19946
    | exact resolve eq19946 eq19946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19946
  have eq23663 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq137 x
       have i₂ := eq23488
       grind)
    | exact superpose eq23488 eq137
    | exact resolve eq137 eq23488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq23488
  have eq23702 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq23663
       have i₂ := eq21903
       grind)
    | exact superpose eq21903 eq23663
    | exact resolve eq23663 eq21903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21903 eq23663
  have eq23855 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23702 eq7865
    | exact resolve eq7865 eq23702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7865
  have eq23976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21904 eq23855
    | exact resolve eq23855 eq21904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23855
  have eq24004 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq23976
       have r₂ := eq28
       grind)
    | exact resolve eq23976 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23976
  have eq25295 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24004 eq507
    | exact resolve eq507 eq24004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq24004
  have eq25301 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25295
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq25295
    | exact resolve eq25295 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq25295
  have eq25317 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23702 eq25301
    | exact resolve eq25301 eq23702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25301
  have eq25318 : (σ (M.op x y)) = (σ y) := by grind
  clear eq25317
  have eq26122 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq25318 eq21904
    | exact resolve eq21904 eq25318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21904 eq25318
  have eq26150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23702 eq26122
    | exact resolve eq26122 eq23702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23702 eq26122
  have eq26468 : False := by grind
  exact eq26468
