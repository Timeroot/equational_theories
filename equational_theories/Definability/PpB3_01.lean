import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
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
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq90 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq81 eq53
    | exact resolve eq53 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq59 eq100
    | exact resolve eq100 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
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
  have eq177 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq199 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = X0 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
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
  have eq295 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 x) x) X0
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 x) x) X0
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 (M.op (M.op x x) x) x
       have r₂ := eq54 x x x
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq307 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq311 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq311 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq311 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq313 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59 eq307
    | exact resolve eq307 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq307
  have eq321 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq200 X0 X0
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq200
    | exact resolve eq200 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq312 (σ X0)
       grind)
    | exact superpose eq312 eq15
    | exact resolve eq15 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq323
    | exact resolve eq323 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq326 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq321 X0
       have i₂ := eq312 (τ X0)
       grind)
    | exact superpose eq312 eq321
    | exact resolve eq321 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq321
  have eq27898 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) ≠ (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302 X1 X1 X2
       have i₂ := eq199 X0 X1
       grind)
    | (have i₁ := eq302 X1 (τ X0) X2
       have i₂ := eq199 X0 X1
       grind)
    | exact superpose eq199 eq302
    | (have j0 := eq302 X0 (τ X1) X2
       have j1 := eq199 X1 X0
       grind)
    | (have r₁ := eq302 (τ X0) (τ X0) X2
       have r₂ := eq199 X0 (τ X0)
       grind)
    | (have r₁ := eq302 X1 (τ X0) X2
       have r₂ := eq199 X0 X1
       grind)
    | exact resolve eq302 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq27909 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq27911 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) ≠ (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq27898 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27898
  have eq27912 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq27911 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27911
  have eq27913 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq27909 X0 X1
       have j1 := eq295 X0 X0 X1
       grind)
    | (have r₁ := eq27909 X1 X1
       have r₂ := eq295 X1 X1 x
       grind)
    | exact resolve eq27909 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27909
  have eq27915 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq27912 X0 X1 X2
       have j1 := eq295 X0 (τ X1) X2
       grind)
    | (have r₁ := eq27912 X0 X1 X2
       have r₂ := eq295 X0 (τ X1) X2
       grind)
    | exact resolve eq27912 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq27912
  have eq27917 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27913 (M.op x x) X1
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq27913
    | exact resolve eq27913 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27913
  have eq28003 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq90 eq27917
    | (have j0 := eq27917 (σ x) (σ y)
       grind)
    | exact resolve eq27917 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq28004 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq78 eq27917
    | exact resolve eq27917 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27917
  have eq28142 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq28003 eq200
    | exact resolve eq200 eq28003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28145 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) (M.op (τ (σ x)) (τ (σ x)))) := by
    first
    | (have i₁ := eq28142
       have i₂ := eq326 sF2
       grind)
    | exact superpose eq326 eq28142
    | exact resolve eq28142 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28142
  have eq28149 : x = (k (τ (M.op (σ x) (σ y))) (M.op x x)) := by
    first
    | exact superpose eq38 eq28145
    | exact resolve eq28145 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28145
  have eq28158 : (τ (M.op (σ x) (σ y))) = (k (τ (σ y)) (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq28004 eq200
    | exact resolve eq200 eq28004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq28004
  have eq28161 : (τ (M.op (σ x) (σ y))) = (k (τ (σ y)) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq28158
       have i₂ := eq326 sF4
       grind)
    | exact superpose eq326 eq28158
    | exact resolve eq28158 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28158
  have eq28166 : (τ (M.op (σ x) (σ y))) = (k y (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq39 eq28161
    | exact resolve eq28161 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28161
  have eq135792 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27915 X1 X0 (M.op (τ X0) x)
       have i₂ := eq53 X1 (τ X0) x
       grind)
    | exact superpose eq53 eq27915
    | (have j0 := eq27915 X1 X0 x
       grind)
    | exact resolve eq27915 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27915
  have eq135802 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ y) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq39 eq135792
    | (have j0 := eq135792 (σ y) X0
       grind)
    | exact resolve eq135792 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135818 : x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq28149
       have i₂ := eq135792 sF4 (M.op x x)
       grind)
    | exact superpose eq135792 eq28149
    | (have j1 := eq135792 (M.op (σ x) (σ y)) (M.op x x)
       grind)
    | exact resolve eq28149 eq135792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28149 eq135792
  have eq135880 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq135818
       have i₂ := eq324 x
       grind)
    | exact superpose eq324 eq135818
    | exact resolve eq135818 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq135818
  have eq135890 : ∀ X0 : G, (σ y) = (σ (k y X0)) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq36 eq135802
    | (have j0 := eq135802 X0
       grind)
    | exact resolve eq135802 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq135802
  have eq135915 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq135880
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq135880
    | exact resolve eq135880 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135880
  have eq135927 : x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28003 eq135915
    | exact resolve eq135915 eq28003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28003 eq135915
  have eq135942 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq135927 eq53
    | exact resolve eq53 eq135927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135927
  have eq135984 : (σ y) = (σ (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) y) := by
    first
    | exact superpose eq28166 eq135890
    | exact resolve eq135890 eq28166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28166
  have eq136156 : ∀ X0 : G, (k y X0) = (τ (σ y)) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 (k y X0)
       have i₂ := eq135890 X0
       grind)
    | exact superpose eq135890 eq10
    | (have j1 := eq135890 X0
       grind)
    | exact resolve eq10 eq135890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135890
  have eq136240 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = (k y X0) := by
    intro X0
    first
    | exact superpose eq39 eq136156
    | (have j0 := eq136156 X0
       grind)
    | exact resolve eq136156 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136156
  have eq136384 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq135984
       have i₂ := eq11 sF4
       grind)
    | exact superpose eq11 eq135984
    | exact resolve eq135984 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135984
  have eq136579 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq136240 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136706 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq136579 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq136579
    | (have j0 := eq136579 x
       grind)
    | exact resolve eq136579 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136579
  have eq138155 : ∀ X0 : G, y = (M.op (τ (M.op (σ x) (σ y))) (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq136384 eq53
    | exact resolve eq53 eq136384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq136384
  have eq138166 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq138155 eq135942
    | exact resolve eq135942 eq138155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138155
  have eq138181 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq138166
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq138166
    | exact resolve eq138166 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138166
  have eq138193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq138181 eq11
    | exact resolve eq11 eq138181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138181
  have eq138493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq138193
    | exact resolve eq138193 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138193
  have eq138495 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq138493
       have r₂ := eq27
       grind)
    | exact resolve eq138493 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138493
  have eq138497 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq138495 eq78
    | exact resolve eq78 eq138495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq138514 : ∀ X0 : G, (τ (σ y)) = (M.op x (M.op (τ (σ y)) X0)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq138495 eq135942
    | exact resolve eq135942 eq138495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135942
  have eq138516 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq138519 : ∀ X0 : G, (τ (σ y)) = (M.op x (M.op (τ (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq138514 X0
       grind)
    | (have r₁ := eq138514 X0
       have r₂ := eq138516
       grind)
    | exact resolve eq138514 eq138516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138514 eq138516
  have eq138530 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq39 eq138519
    | exact resolve eq138519 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138519
  have eq138532 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq138497 eq138497
    | exact resolve eq138497 eq138497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138497
  have eq138556 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq138532
  have eq138614 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq138556 eq326
    | exact resolve eq326 eq138556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138556
  have eq138675 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39 eq138614
    | exact resolve eq138614 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq138614
  have eq139817 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq138530 y
       have i₂ := eq138675
       grind)
    | exact superpose eq138675 eq138530
    | exact resolve eq138530 eq138675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138530 eq138675
  have eq139837 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq139817
  have eq139838 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq139837
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq139837
    | exact resolve eq139837 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139837
  have eq139840 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq139838 eq27
    | exact resolve eq27 eq139838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139846 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq139838 eq102
    | (have r₁ := eq102
       have r₂ := eq139838
       grind)
    | exact resolve eq102 eq139838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139861 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq139846
  have eq139874 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq139861
       have i₂ := eq136240 x
       grind)
    | exact superpose eq136240 eq139861
    | (have j1 := eq136240 x
       grind)
    | exact resolve eq139861 eq136240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139896 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq139861
       grind)
    | exact superpose eq139861 eq10
    | exact resolve eq10 eq139861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140040 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq139896
    | exact resolve eq139896 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139896
  have eq140058 : (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq139874
       have r₂ := eq136706
       grind)
    | exact resolve eq139874 eq136706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139874
  have eq140079 : (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq140058
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq140058
    | exact resolve eq140058 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140058
  have eq140093 : y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq140079
    | exact resolve eq140079 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140079
  have eq140497 : (σ y) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq139861
       have i₂ := eq140093
       grind)
    | exact superpose eq140093 eq139861
    | exact resolve eq139861 eq140093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139861
  have eq140498 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq140040
       have i₂ := eq140093
       grind)
    | exact superpose eq140093 eq140040
    | exact resolve eq140040 eq140093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140040 eq140093
  have eq140508 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq140498
       have r₂ := eq139840
       grind)
    | exact resolve eq140498 eq139840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140498
  have eq140509 : (σ y) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq140497
       have r₂ := eq139840
       grind)
    | exact resolve eq140497 eq139840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139840 eq140497
  have eq140515 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq140509
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq140509
    | exact resolve eq140509 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140509
  have eq140518 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq140508 eq20
    | exact resolve eq20 eq140508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140508
  have eq140728 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq140518
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq140518
    | exact resolve eq140518 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140518
  have eq140733 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq140515 eq26
    | exact resolve eq26 eq140515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq140515
  have eq141197 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq140733 eq313
    | (have r₁ := eq313
       have r₂ := eq140733
       grind)
    | exact resolve eq313 eq140733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq141223 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq140733 eq81
    | exact resolve eq81 eq140733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq140733
  have eq141269 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq141197
  have eq141297 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq141269
       have r₂ := eq102
       grind)
    | exact resolve eq141269 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141269
  have eq141404 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq139838 eq141223
    | exact resolve eq141223 eq139838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139838 eq141223
  have eq141456 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq141404
  have eq141518 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq141456 eq326
    | exact resolve eq326 eq141456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq141456
  have eq141583 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq141518
    | exact resolve eq141518 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq141518
  have eq143272 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq141297
       have i₂ := eq136240 x
       grind)
    | exact superpose eq136240 eq141297
    | (have j1 := eq136240 x
       grind)
    | exact resolve eq141297 eq136240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136240 eq141297
  have eq143435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq143272
       have r₂ := eq136706
       grind)
    | exact resolve eq143272 eq136706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136706 eq143272
  have eq143457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq143435
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq143435
    | exact resolve eq143435 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143435
  have eq143467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq20 eq143457
    | exact resolve eq143457 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143457
  have eq143470 : y = (k y x) := by
    first
    | (have r₁ := eq143467
       have r₂ := eq27
       grind)
    | exact resolve eq143467 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143467
  have eq143474 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq143470
       grind)
    | exact superpose eq143470 eq102
    | exact resolve eq102 eq143470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq143470
  have eq143848 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq143474
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq143474
    | exact resolve eq143474 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143474
  have eq143866 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq143848
       have r₂ := eq138495
       grind)
    | exact resolve eq143848 eq138495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138495 eq143848
  have eq143876 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq143866 eq27
    | exact resolve eq27 eq143866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq143866
  have eq146259 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq140728 eq143876
    | (have r₁ := eq143876
       have r₂ := eq140728
       grind)
    | exact resolve eq143876 eq140728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140728
  have eq146261 : x = y := by grind
  clear eq146259
  have eq146262 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq146261
       grind)
    | exact superpose eq146261 eq18
    | exact resolve eq18 eq146261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq146263 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq146261
       grind)
    | exact superpose eq146261 eq24
    | exact resolve eq24 eq146261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq160632 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq141583
       have i₂ := eq146261
       grind)
    | exact superpose eq146261 eq141583
    | exact resolve eq141583 eq146261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141583 eq146261
  have eq162421 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq146263
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq146263
    | exact resolve eq146263 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146263
  have eq162820 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq160632
       have i₂ := eq146262
       grind)
    | exact superpose eq146262 eq160632
    | exact resolve eq160632 eq146262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146262 eq160632
  have eq162890 : x = (M.op x y) := by grind
  clear eq162820
  have eq163613 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq162421 eq143876
    | exact resolve eq143876 eq162421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143876 eq162421
  have eq167364 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq162890 eq20
    | exact resolve eq20 eq162890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq162890
  have eq178516 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq167364
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167364
    | exact resolve eq167364 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq167364
  have eq179688 : False := by grind
  exact eq179688

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
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
  have eq177 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq756 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq760 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28
  have eq848 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq848 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq848 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq848 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq848 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq848 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq1251 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq40
    | exact resolve eq40 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1252 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1251
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1251
    | exact resolve eq1251 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1254 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq1252
    | exact resolve eq1252 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1254 eq760
    | exact resolve eq760 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1269 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1262
       have r₂ := eq27
       grind)
    | exact resolve eq1262 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1274 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1269 eq185
    | exact resolve eq185 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1275 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1269 eq189
    | exact resolve eq189 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq1269
  have eq1292 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1275
       have i₂ := eq849 sF4
       grind)
    | exact superpose eq849 eq1275
    | exact resolve eq1275 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1293 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1274
       have i₂ := eq849 sF4
       grind)
    | exact superpose eq849 eq1274
    | exact resolve eq1274 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1297 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1292 eq1293
    | exact resolve eq1293 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292 eq1293
  have eq1304 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq184 x
       have i₂ := eq1297
       grind)
    | exact superpose eq1297 eq184
    | exact resolve eq184 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1305 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq188 y
       have i₂ := eq1297
       grind)
    | exact superpose eq1297 eq188
    | exact resolve eq188 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq1297
  have eq1322 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1305
       have i₂ := eq849 sF0
       grind)
    | exact superpose eq849 eq1305
    | exact resolve eq1305 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1323 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1304
       have i₂ := eq849 sF0
       grind)
    | exact superpose eq849 eq1304
    | exact resolve eq1304 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1327 : (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1322 eq1323
    | exact resolve eq1323 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq1323
  have eq1331 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1327 eq32
    | exact resolve eq32 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1327
  have eq1364 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq1331
    | exact resolve eq1331 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1331
  have eq1365 : x = y := by grind
  clear eq1364
  have eq1369 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1365
       grind)
    | exact superpose eq1365 eq24
    | exact resolve eq24 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1376 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq756
       have i₂ := eq1365
       grind)
    | exact superpose eq1365 eq756
    | exact resolve eq756 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq1365
  have eq1382 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1376
       have i₂ := eq849 x
       grind)
    | exact superpose eq849 eq1376
    | exact resolve eq1376 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq1383 : (M.op x y) = (k x x) := by grind
  clear eq1382
  have eq1387 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1369
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1369
    | exact resolve eq1369 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1404 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1387 eq760
    | exact resolve eq760 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq1387
  have eq1412 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1404
       have i₂ := eq849 sF2
       grind)
    | exact superpose eq849 eq1404
    | exact resolve eq1404 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq1404
  have eq1413 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1412
  have eq1430 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1383
       grind)
    | exact superpose eq1383 eq40
    | exact resolve eq40 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1383
  have eq1434 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1430
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1430
    | exact resolve eq1430 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1430
  have eq1437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1413 eq1434
    | exact resolve eq1434 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413 eq1434
  have eq1439 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1437
    | exact resolve eq1437 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1437
  have eq1441 : False := by grind
  exact eq1441

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33
    | exact resolve eq33 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq42
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq42 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq172 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq593 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq186 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq186
    | (have j0 := eq186 (τ X0) (τ X1)
       grind)
    | exact resolve eq186 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq593
    | (have j0 := eq593 X0 X1
       grind)
    | exact resolve eq593 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq603 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq600
    | (have j0 := eq600 X0 X1
       grind)
    | exact resolve eq600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq605 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq603
    | (have j0 := eq603 X0 X1
       grind)
    | exact resolve eq603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq606 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq605
    | (have j0 := eq605 X0 X1
       grind)
    | exact resolve eq605 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq607 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq606
    | (have j0 := eq606 X0 X1
       grind)
    | exact resolve eq606 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq608 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq607 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq607
    | (have j0 := eq607 X0 X1
       grind)
    | exact resolve eq607 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq3640 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq83 X1 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq83 X0 (σ X0)
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3656 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq83 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq3657 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3656 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3656
  have eq3658 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3640 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3640
  have eq3659 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3658
  have eq3662 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3657 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3657
    | (have j0 := eq3657 X0
       grind)
    | exact resolve eq3657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3657
  have eq3700 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq3662 X0
       grind)
    | exact superpose eq3662 eq49
    | (have j1 := eq3662 X0
       grind)
    | exact resolve eq49 eq3662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3662
  have eq3723 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3700 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3700
    | (have j0 := eq3700 X0
       grind)
    | exact resolve eq3700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3700
  have eq3724 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3723 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723
  have eq3728 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3724 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3724
    | exact resolve eq3724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3752 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3724 X0
       grind)
    | exact superpose eq3724 eq11
    | exact resolve eq11 eq3724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3797 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3728 X0
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq3728
    | exact resolve eq3728 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728
  have eq3875 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3797 X0
       grind)
    | exact superpose eq3797 eq11
    | exact resolve eq11 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3956 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3875 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3875
    | exact resolve eq3875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3875
  have eq4018 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45 X0 X0
       have i₂ := eq3956 (τ X0)
       grind)
    | exact superpose eq3956 eq45
    | exact resolve eq45 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4069 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4018 X0
       have i₂ := eq3797 X0
       grind)
    | exact superpose eq3797 eq4018
    | exact resolve eq4018 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3797 eq4018
  have eq4410 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4438 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4410 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4410
    | exact resolve eq4410 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4410
  have eq4474 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4438 X0
       have i₂ := eq3956 X0
       grind)
    | exact superpose eq3956 eq4438
    | exact resolve eq4438 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4438
  have eq4494 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq4474
  have eq99479 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3659 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3659
    | exact resolve eq3659 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99607 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) X0
       have i₂ := eq3659 (σ X0) X1
       grind)
    | exact superpose eq3659 eq33
    | (have j1 := eq3659 (σ X0) X1
       grind)
    | exact resolve eq33 eq3659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3659
  have eq99734 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq99607 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq99607
    | (have j0 := eq99607 X0 X1
       grind)
    | exact resolve eq99607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99607
  have eq99807 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99479 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq99479
    | (have j0 := eq99479 X0 X1
       grind)
    | exact resolve eq99479 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99479
  have eq99847 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq99734 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99734
    | (have j0 := eq99734 X0 X1
       grind)
    | exact resolve eq99734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99734
  have eq99934 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq99847 X0 X1
       have i₂ := eq3752 X0
       grind)
    | exact superpose eq3752 eq99847
    | (have j0 := eq99847 X0 X1
       grind)
    | exact resolve eq99847 eq3752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99847
  have eq99985 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq99934 X0 X1
       have i₂ := eq3956 X0
       grind)
    | exact superpose eq3956 eq99934
    | (have j0 := eq99934 X0 X1
       grind)
    | exact resolve eq99934 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99934
  have eq100029 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq99985 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99985
    | (have j0 := eq99985 X0 X1
       grind)
    | exact resolve eq99985 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99985
  have eq100251 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq99807 X0 X1
       grind)
    | exact superpose eq99807 eq11
    | (have j1 := eq99807 X0 X1
       grind)
    | exact resolve eq11 eq99807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99807
  have eq100509 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq100251 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq100251
    | (have j0 := eq100251 X0 X1
       grind)
    | exact resolve eq100251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100251
  have eq102329 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq100509 (τ X0) X1
       grind)
    | exact superpose eq100509 eq18
    | (have j1 := eq100509 (τ X0) X1
       grind)
    | exact resolve eq18 eq100509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq100509
  have eq111944 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq100029 (τ X0) (τ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq100029
    | (have j0 := eq100029 (τ X1) (τ X0)
       grind)
    | exact resolve eq100029 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq100029
  have eq112405 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq111944 X0 X1
       have i₂ := eq4069 X1
       grind)
    | exact superpose eq4069 eq111944
    | (have j0 := eq111944 X0 X1
       grind)
    | exact resolve eq111944 eq4069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111944
  have eq112604 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq112405 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq112405
    | (have j0 := eq112405 X0 X1
       grind)
    | exact resolve eq112405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112405
  have eq112763 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq112604 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq112604
    | (have j0 := eq112604 X0 X1
       grind)
    | exact resolve eq112604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112604
  have eq112893 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112763 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq112763
    | (have j0 := eq112763 X0 X1
       grind)
    | exact resolve eq112763 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112763
  have eq112984 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112893 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq112893
    | (have j0 := eq112893 X0 X1
       grind)
    | exact resolve eq112893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112893
  have eq114966 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq112984 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112984
  have eq119015 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq102329 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102329
    | exact resolve eq102329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102329
  have eq119373 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq119015 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq119015
    | (have j0 := eq119015 X0 X1
       grind)
    | exact resolve eq119015 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119015
  have eq119876 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op X1 (τ X0))) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq119373 X1 (τ X0)
       grind)
    | exact superpose eq119373 eq19
    | (have j1 := eq119373 X1 (τ X0)
       grind)
    | exact resolve eq19 eq119373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119373
  have eq120246 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op X1 (τ X0))) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119876 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq119876
    | (have j0 := eq119876 X0 X1
       grind)
    | exact resolve eq119876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119876
  have eq120419 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (k (σ X1) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq120246 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq120246
    | (have j0 := eq120246 X0 X1
       grind)
    | exact resolve eq120246 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq120246
  have eq120556 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq120419 X0 X1
       have i₂ := eq4069 X0
       grind)
    | exact superpose eq4069 eq120419
    | (have j0 := eq120419 X0 X1
       grind)
    | exact resolve eq120419 eq4069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4069 eq120419
  have eq132911 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq120556 (σ X1) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq120556
    | (have j0 := eq120556 (σ X1) X0
       grind)
    | exact resolve eq120556 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120556
  have eq133187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132911 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq132911
    | (have j0 := eq132911 X0 X1
       grind)
    | exact resolve eq132911 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132911
  have eq133322 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq133187 X0 X1
       have i₂ := eq3724 X1
       grind)
    | exact superpose eq3724 eq133187
    | (have j0 := eq133187 X0 X1
       grind)
    | exact resolve eq133187 eq3724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724 eq133187
  have eq133422 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq133322 X0 X1
       have i₂ := eq3956 X1
       grind)
    | exact superpose eq3956 eq133322
    | (have j0 := eq133322 X0 X1
       grind)
    | exact resolve eq133322 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133322
  have eq133873 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq172
       have i₂ := eq133422 x y
       grind)
    | exact superpose eq133422 eq172
    | (have j1 := eq133422 x y
       grind)
    | (have r₁ := eq172
       have r₂ := eq133422 x y
       grind)
    | exact resolve eq172 eq133422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq133422
  have eq134043 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq133873
  have eq134136 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq186 x y
       grind)
    | (have r₁ := eq134043
       have r₂ := eq186 x y
       grind)
    | exact resolve eq134043 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq134043
  have eq134336 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq134136
       have i₂ := eq3752 y
       grind)
    | exact superpose eq3752 eq134136
    | exact resolve eq134136 eq3752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134136
  have eq134458 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq134336
       have i₂ := eq3956 y
       grind)
    | exact superpose eq3956 eq134336
    | exact resolve eq134336 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134336
  have eq138706 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134458
       grind)
    | exact superpose eq134458 eq16
    | exact resolve eq16 eq134458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138758 : (τ (σ y)) ≠ (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq114966 (σ x) (σ y)
       have i₂ := eq134458
       grind)
    | exact superpose eq134458 eq114966
    | (have j0 := eq114966 (σ x) (σ y)
       grind)
    | exact resolve eq114966 eq134458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114966 eq134458
  have eq138761 : (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq138758
  have eq138767 : (σ x) = (σ (k y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq138761
       have i₂ := eq3752 y
       grind)
    | exact superpose eq3752 eq138761
    | exact resolve eq138761 eq3752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3752 eq138761
  have eq138790 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq138767
       have i₂ := eq3956 y
       grind)
    | exact superpose eq3956 eq138767
    | exact resolve eq138767 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956 eq138767
  have eq138791 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ x = (M.op y y) := by grind
  clear eq138790
  have eq138809 : (τ (σ y)) = (k (τ (σ x)) y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq138791
       have i₂ := eq33 (σ x) y
       grind)
    | exact superpose eq33 eq138791
    | exact resolve eq138791 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq138791
  have eq138814 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq138809
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq138809
    | exact resolve eq138809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138809
  have eq138818 : y = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq138814
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq138814
    | exact resolve eq138814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138814
  have eq138831 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq608 x y
       have i₂ := eq138818
       grind)
    | exact superpose eq138818 eq608
    | (have j0 := eq608 x y
       grind)
    | (have r₁ := eq608 x y
       have r₂ := eq138818
       grind)
    | exact resolve eq608 eq138818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq138818
  have eq138851 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq138831
  have eq138852 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq138851
  have eq139736 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq138706
       have i₂ := eq138852
       grind)
    | exact superpose eq138852 eq138706
    | exact resolve eq138706 eq138852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138706 eq138852
  have eq139740 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq139736
  have eq139741 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq139740
  have eq140704 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4494 y
       have i₂ := eq139741
       grind)
    | exact superpose eq139741 eq4494
    | exact resolve eq4494 eq139741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139741
  have eq140849 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq140704
       have r₂ := eq16
       grind)
    | exact resolve eq140704 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140704
  have eq140903 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq140849
       grind)
    | exact superpose eq140849 eq10
    | exact resolve eq10 eq140849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140849
  have eq141229 : x = (M.op y y) := by
    first
    | (have i₁ := eq140903
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq140903
    | exact resolve eq140903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140903
  have eq142252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4494 y
       have i₂ := eq141229
       grind)
    | exact superpose eq141229 eq4494
    | exact resolve eq4494 eq141229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4494 eq141229
  have eq142398 : False := by grind
  exact eq142398

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  clear eq18
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq62 X2 X0 x
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq62 X3 X0 x
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq465 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ X0 = X1 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op x x)
       have i₂ := eq62 x x x
       grind)
    | exact superpose eq62 eq13
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq469 (σ X0)
       grind)
    | exact superpose eq469 eq15
    | (have j1 := eq469 (σ X0)
       grind)
    | exact resolve eq15 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq512 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 (M.op X0 X1)
       have i₂ := eq62 X0 X0 X1
       grind)
    | exact superpose eq62 eq465
    | (have j0 := eq465 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq465 x (M.op x x)
       have r₂ := eq62 x x x
       grind)
    | exact resolve eq465 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq514 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq512 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq550 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq480
  have eq552 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq550 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq550
    | (have j0 := eq550 X0
       grind)
    | exact resolve eq550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq553 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq552 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq578 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq594 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq553 X0
       grind)
    | exact superpose eq553 eq578
    | (have j0 := eq578 X0 X1
       grind)
    | exact resolve eq578 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq605 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq553 X0
       grind)
    | exact superpose eq553 eq594
    | (have j0 := eq594 X0 X1
       grind)
    | exact resolve eq594 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq614 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq553 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq553
    | exact resolve eq553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ X0) (σ X0)
       have i₂ := eq553 X0
       grind)
    | exact superpose eq553 eq62
    | exact resolve eq62 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq73 (σ X0)
       have i₂ := eq553 X0
       grind)
    | exact superpose eq553 eq73
    | exact resolve eq73 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq553
  have eq640 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq638 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq638
    | exact resolve eq638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq641 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq637 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq637
    | exact resolve eq637 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq647 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq614 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq614
    | exact resolve eq614 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq650 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq647 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq647
    | exact resolve eq647 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq669 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq650 (τ X0)
       grind)
    | exact superpose eq650 eq32
    | exact resolve eq32 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq669 X0
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq669
    | exact resolve eq669 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq752 : ∀ X0 X1 : G, (τ X0) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq514 (τ X0) X1
       have i₂ := eq676 X0
       grind)
    | exact superpose eq676 eq514
    | (have j0 := eq514 (τ X0) X1
       grind)
    | exact resolve eq514 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq796 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq625 (k X0 X0) (M.op x (σ X0))
       have i₂ := eq625 X0 x
       grind)
    | exact superpose eq625 eq625
    | exact resolve eq625 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq829 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq796 X0
       have i₂ := eq650 (k X0 X0)
       grind)
    | exact superpose eq650 eq796
    | exact resolve eq796 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq841 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq829 X0
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq829
    | exact resolve eq829 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq848 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq841 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq841 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq841
    | exact resolve eq841 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq1453 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k (k X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ X0) (σ (k X0 X0))
       have i₂ := eq640 X0
       grind)
    | exact superpose eq640 eq62
    | exact resolve eq62 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq1467 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1453 X0 X1
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq1453
    | exact resolve eq1453 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453
  have eq1492 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    grind
  clear eq1467
  have eq1579 : ∀ X0 X1 X2 : G, (σ (k X0 (k X0 X0))) = (M.op (M.op (M.op X1 X2) (σ (k X0 (k X0 X0)))) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (σ X0) X1 X2 (σ (k X0 X0))
       have i₂ := eq641 X0
       grind)
    | exact superpose eq641 eq70
    | exact resolve eq70 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq641
  have eq1582 : ∀ X0 X1 X2 : G, (σ (k X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 X2) (σ (k X0 (M.op X0 X0)))) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1579 X0 X1 X2
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq1579
    | exact resolve eq1579 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579
  have eq1607 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X1 X2) (σ (M.op (M.op X0 X0) X0))) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1582 X0 X1 X2
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq1582
    | exact resolve eq1582 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1582
  have eq3082 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq605 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq3085 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3082 X0 X1
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq3082
    | (have j0 := eq3082 X0 X1
       grind)
    | exact resolve eq3082 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082
  have eq3120 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3085 X0 X1
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq3085
    | (have j0 := eq3085 X0 X1
       grind)
    | exact resolve eq3085 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085
  have eq3153 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3120 X0 X1
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq3120
    | (have j0 := eq3120 X0 X1
       grind)
    | exact resolve eq3120 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq3120
  have eq11141 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X0 X0) (M.op (τ X0) X1)
       have i₂ := eq752 X0 X1
       grind)
    | exact superpose eq752 eq19
    | (have j1 := eq752 X0 X1
       grind)
    | exact resolve eq19 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq752
  have eq11143 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) (M.op X0 X0)) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11141 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11141
    | (have j0 := eq11141 X0 X1
       grind)
    | exact resolve eq11141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11141
  have eq11288 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op (τ (σ X0)) X1)) (σ (M.op X0 X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11143 (σ X0) X1
       have i₂ := eq848 X0
       grind)
    | exact superpose eq848 eq11143
    | (have j0 := eq11143 (σ X0) X1
       grind)
    | exact resolve eq11143 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11143
  have eq11309 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op (τ (σ X0)) X1) (M.op X0 X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11288 X0 X1
       have i₂ := eq15 (M.op (τ (σ X0)) X1) (M.op X0 X0)
       grind)
    | exact superpose eq15 eq11288
    | (have j0 := eq11288 X0 X1
       grind)
    | exact resolve eq11288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11288
  have eq11343 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X0 X1) (M.op X0 X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11309 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11309
    | (have j0 := eq11309 X0 X1
       grind)
    | exact resolve eq11309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11309
  have eq11367 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X0 X1) (M.op X0 X0))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11343 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11343
    | (have j0 := eq11343 X0 X1
       grind)
    | exact resolve eq11343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11343
  have eq11424 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (σ (k X0 (M.op (M.op X1 X0) (M.op X1 X0)))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11367 (M.op X0 x) (M.op x x)
       have i₂ := eq62 X0 x x
       grind)
    | exact superpose eq62 eq11367
    | exact resolve eq11367 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43183 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3153 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3153
    | (have j0 := eq3153 (τ X1) (τ X0)
       grind)
    | exact resolve eq3153 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43207 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3153 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq11367 X0 X1
       grind)
    | exact superpose eq11367 eq3153
    | (have j0 := eq3153 (M.op X0 X0) (M.op X0 X1)
       have j1 := eq11367 X0 X1
       grind)
    | exact resolve eq3153 eq11367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153
  have eq43255 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43207 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq43207 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq43207
    | (have j0 := eq43207 X0 X1
       grind)
    | exact resolve eq43207 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43207
  have eq43256 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43255 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43255
  have eq43272 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43183 X0 X1
       have i₂ := eq676 X1
       grind)
    | exact superpose eq676 eq43183
    | (have j0 := eq43183 X0 X1
       grind)
    | exact resolve eq43183 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43183
  have eq43306 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43256 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq43256 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq43256
    | (have j0 := eq43256 X0 X1
       grind)
    | exact resolve eq43256 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43256
  have eq43322 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43272 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq43272
    | (have j0 := eq43272 X0 X1
       grind)
    | exact resolve eq43272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43272
  have eq43350 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43306 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq43306 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq43306
    | (have j0 := eq43306 X0 X1
       grind)
    | exact resolve eq43306 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43306
  have eq43366 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43322 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq43322
    | (have j0 := eq43322 X0 X1
       grind)
    | exact resolve eq43322 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43322
  have eq43406 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43366 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43366
    | (have j0 := eq43366 X0 X1
       grind)
    | exact resolve eq43366 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43366
  have eq43438 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43406 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq43406
    | (have j0 := eq43406 X0 X1
       grind)
    | exact resolve eq43406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43406
  have eq43467 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43438 X0 X1
       have i₂ := eq676 X1
       grind)
    | exact superpose eq676 eq43438
    | (have j0 := eq43438 X0 X1
       grind)
    | exact resolve eq43438 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43438
  have eq43489 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43467 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq43467
    | (have j0 := eq43467 X0 X1
       grind)
    | exact resolve eq43467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43467
  have eq43507 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43489 X0 X1
       have i₂ := eq676 X1
       grind)
    | exact superpose eq676 eq43489
    | (have j0 := eq43489 X0 X1
       grind)
    | exact resolve eq43489 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq43489
  have eq43521 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43507 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq43507
    | (have j0 := eq43507 X0 X1
       grind)
    | exact resolve eq43507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43507
  have eq43533 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43521 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43521
    | (have j0 := eq43521 X0 X1
       grind)
    | exact resolve eq43521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43521
  have eq43552 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43533 X0 (M.op x x)
       have i₂ := eq62 x x x
       grind)
    | exact superpose eq62 eq43533
    | exact resolve eq43533 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43533
  have eq210809 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X1) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X1)
       have i₂ := eq43350 X0 X1
       grind)
    | exact superpose eq43350 eq10
    | (have j1 := eq43350 X0 X1
       grind)
    | exact resolve eq10 eq43350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43350
  have eq211037 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq210809 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq210809
    | (have j0 := eq210809 X0 X1
       grind)
    | exact resolve eq210809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210809
  have eq211038 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq211037 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211037
  have eq212630 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (M.op (σ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ (M.op X0 X0)) (σ (M.op X0 X1)) X2
       have i₂ := eq211038 X0 X1
       grind)
    | exact superpose eq211038 eq62
    | (have j1 := eq211038 X0 X1
       grind)
    | exact resolve eq62 eq211038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212634 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (σ (M.op X0 X1)) X1 (σ (M.op X0 X0))
       have i₂ := eq211038 X0 X1
       grind)
    | exact superpose eq211038 eq68
    | (have j1 := eq211038 X0 X1
       grind)
    | exact resolve eq68 eq211038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq211038
  have eq214745 : ∀ X0 X1 X2 : G, (σ (M.op X1 X0)) = (M.op (M.op X2 (σ (M.op X1 X0))) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212634 (M.op X0 x) (M.op x x) X2
       have i₂ := eq62 X0 x x
       grind)
    | exact superpose eq62 eq212634
    | exact resolve eq212634 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212634
  have eq216923 : ∀ X0 X1 X3 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X3)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq212630 (M.op X0 x) (M.op x x) x
       have i₂ := eq62 X0 x x
       grind)
    | exact superpose eq62 eq212630
    | exact resolve eq212630 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218236 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq212630 X1 X0 (M.op (σ X0) x)
       have i₂ := eq216923 X0 X1 x
       grind)
    | exact superpose eq216923 eq212630
    | (have j0 := eq212630 X1 X0 x
       have j1 := eq216923 X0 X1 x
       grind)
    | exact resolve eq212630 eq216923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212630 eq216923
  have eq228302 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq218236 y x
       grind)
    | exact superpose eq218236 eq16
    | (have j1 := eq218236 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq218236 y x
       grind)
    | exact resolve eq16 eq218236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218236
  have eq229183 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq228302
  have eq230406 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq62 x y X0
       have i₂ := eq229183
       grind)
    | exact superpose eq229183 eq62
    | exact resolve eq62 eq229183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230433 : (σ x) = (σ (k y (M.op x x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11367 x y
       have i₂ := eq229183
       grind)
    | exact superpose eq229183 eq11367
    | (have j0 := eq11367 x y
       grind)
    | exact resolve eq11367 eq229183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11367
  have eq230493 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq229183
  have eq230544 : x = (M.op x y) ∨ (σ x) = (σ (k y (M.op x x))) := by
    first
    | (have r₁ := eq230433
       have r₂ := eq230493
       grind)
    | exact resolve eq230433 eq230493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230433 eq230493
  have eq230613 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op y (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 x y
       have i₂ := eq230406 X1
       grind)
    | exact superpose eq230406 eq62
    | (have j1 := eq230406 X1
       grind)
    | exact resolve eq62 eq230406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230940 : (σ x) = (σ (k y (M.op x x))) ∨ x = y ∨ (σ x) = (σ (k y (M.op x x))) := by
    first
    | (have i₁ := eq11424 y x
       have i₂ := eq230544
       grind)
    | exact superpose eq230544 eq11424
    | exact resolve eq11424 eq230544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11424 eq230544
  have eq230970 : x = y ∨ (σ x) = (σ (k y (M.op x x))) := by grind
  clear eq230940
  have eq231866 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y (M.op x x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq230970
       grind)
    | exact superpose eq230970 eq16
    | exact resolve eq16 eq230970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230970
  have eq231881 : (σ x) = (σ (k y (M.op x x))) := by
    first
    | (have r₁ := eq231866
       have r₂ := eq848 x
       grind)
    | exact resolve eq231866 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231866
  have eq231890 : (k y (M.op x x)) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y (M.op x x))
       have i₂ := eq231881
       grind)
    | exact superpose eq231881 eq10
    | exact resolve eq10 eq231881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231881
  have eq232114 : x = (k y (M.op x x)) := by
    first
    | (have i₁ := eq231890
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq231890
    | exact resolve eq231890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231890
  have eq232197 : x ≠ x ∨ x = (M.op (M.op x x) y) ∨ x = y := by
    first
    | (have i₁ := eq43552 x y
       have i₂ := eq232114
       grind)
    | exact superpose eq232114 eq43552
    | (have j0 := eq43552 x y
       grind)
    | (have r₁ := eq43552 x y
       have r₂ := eq232114
       grind)
    | exact resolve eq43552 eq232114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43552 eq232114
  have eq232208 : x = y ∨ x = (M.op (M.op x x) y) := by grind
  clear eq232197
  have eq232225 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq232208
       grind)
    | exact superpose eq232208 eq16
    | exact resolve eq16 eq232208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232208
  have eq232244 : x = (M.op (M.op x x) y) := by
    first
    | (have r₁ := eq232225
       have r₂ := eq848 x
       grind)
    | exact resolve eq232225 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232225
  have eq232261 : ∀ X0 : G, y = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op x x) y X0
       have i₂ := eq232244
       grind)
    | exact superpose eq232244 eq62
    | exact resolve eq62 eq232244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq232365 : ∀ X0 : G, x = y ∨ (σ x) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq214745 y (M.op x x) x
       have i₂ := eq232244
       grind)
    | exact superpose eq232244 eq214745
    | exact resolve eq214745 eq232244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214745 eq232244
  have eq237819 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq232365 X0
       grind)
    | exact superpose eq232365 eq16
    | (have j1 := eq232365 X0
       grind)
    | exact resolve eq16 eq232365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232365
  have eq237860 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq237819 X0
       grind)
    | (have r₁ := eq237819 X0
       have r₂ := eq848 x
       grind)
    | exact resolve eq237819 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq237819
  have eq237878 : (σ x) = (M.op (σ (M.op (M.op x x) x)) (σ y)) := by
    first
    | (have i₁ := eq237860 (M.op (M.op x x) (σ (M.op (M.op x x) x)))
       have i₂ := eq1607 x x x
       grind)
    | exact superpose eq1607 eq237860
    | exact resolve eq237860 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq237910 : (σ y) = (M.op (σ x) (σ (M.op y (M.op y y)))) := by
    first
    | (have i₁ := eq1492 y (M.op x (σ x))
       have i₂ := eq237860 x
       grind)
    | exact superpose eq237860 eq1492
    | exact resolve eq1492 eq237860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492 eq237860
  have eq242447 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq237878
       have i₂ := eq230613 x X0
       grind)
    | exact superpose eq230613 eq237878
    | (have j1 := eq230613 X0 X0
       grind)
    | exact resolve eq237878 eq230613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230613 eq237878
  have eq249758 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq242447 X0
       grind)
    | exact superpose eq242447 eq16
    | (have j1 := eq242447 X0
       grind)
    | exact resolve eq16 eq242447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242447
  have eq250001 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ y = (M.op y (M.op y X0)) ∨ y = (M.op y (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq249758 X0
       have i₂ := eq230406 X1
       grind)
    | exact superpose eq230406 eq249758
    | (have j0 := eq249758 X0
       have j1 := eq230406 X0
       grind)
    | exact resolve eq249758 eq230406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230406 eq249758
  have eq250027 : ∀ X0 X1 : G, y = (M.op y (M.op y X0)) ∨ y = (M.op y (M.op y X1)) := by
    intro X0 X1
    first
    | (have j0 := eq250001 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250001
  have eq250551 : ∀ X0 : G, y ≠ y ∨ y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have j0 := eq250027 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250027
  have eq250552 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have j0 := eq250551 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250551
  have eq250573 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq237910
       have i₂ := eq250552 y
       grind)
    | exact superpose eq250552 eq237910
    | exact resolve eq237910 eq250552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237910
  have eq250579 : y = (M.op x y) := by
    first
    | (have i₁ := eq232261 (M.op y x)
       have i₂ := eq250552 x
       grind)
    | exact superpose eq250552 eq232261
    | exact resolve eq232261 eq250552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232261 eq250552
  have eq251756 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq250573
       grind)
    | exact superpose eq250573 eq16
    | exact resolve eq16 eq250573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250573
  have eq251983 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq251756
       have i₂ := eq250579
       grind)
    | exact superpose eq250579 eq251756
    | exact resolve eq251756 eq250579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250579 eq251756
  have eq251984 : False := by grind
  exact eq251984

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq21 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq32 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33
    | exact resolve eq33 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq170 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq82
    | exact resolve eq82 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X1) (σ X0) X2
       have i₂ := eq82 X1 X0
       grind)
    | exact superpose eq82 eq20
    | (have j1 := eq82 X1 X0
       grind)
    | exact resolve eq20 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (M.op (σ (k X0 X1)) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X0) (σ X1) x
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq21
    | (have j1 := eq82 X1 X0
       grind)
    | exact resolve eq21 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq82
  have eq1169 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 (τ X0) (τ X1) X2
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq177
    | (have j0 := eq177 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq177 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1210 : ∀ X0 X1 X2 : G, (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1169 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1169
    | (have j0 := eq1169 X0 X1 X2
       grind)
    | exact resolve eq1169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1215 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1210 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1210
    | (have j0 := eq1210 X0 X1 X2
       grind)
    | exact resolve eq1210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1219 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1215 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1215
    | (have j0 := eq1215 X0 X1 X2
       grind)
    | exact resolve eq1215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1222 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1219 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1219
    | (have j0 := eq1219 X0 X1 X2
       grind)
    | exact resolve eq1219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1225 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op (k X0 X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1222 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1222
    | (have j0 := eq1222 X0 X1 X2
       grind)
    | exact resolve eq1222 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1226 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1225 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1225
    | (have j0 := eq1225 X0 X1 X2
       grind)
    | exact resolve eq1225 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1423 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ (k X0 X0)) = (M.op (σ X0) (M.op (σ (k X0 X0)) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1424 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (M.op (σ (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1423 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq2756 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq170 X0 X1 X2
       grind)
    | exact superpose eq170 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq170 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq170 X0 X1 X2
       grind)
    | exact resolve eq13 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2769 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2756 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2756
  have eq2770 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2769 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769
  have eq2771 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2770 X0 X1 X2
       have i₂ := eq32 X0 X1 X2
       grind)
    | exact superpose eq32 eq2770
    | (have j0 := eq2770 X0 X1 X2
       grind)
    | exact resolve eq2770 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2770
  have eq3675 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) = (M.op X0 (M.op (σ (k (τ X0) (τ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1424 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1424
    | exact resolve eq1424 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424
  have eq3724 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = (M.op X0 (M.op (k (σ (τ X0)) X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3675 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3675
    | (have j0 := eq3675 X0 X1
       grind)
    | exact resolve eq3675 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3675
  have eq3725 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3724 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3724
    | (have j0 := eq3724 X0 X1
       grind)
    | exact resolve eq3724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq3731 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3725 X0 (M.op X0 x)
       have i₂ := eq1226 X0 X0 x
       grind)
    | exact superpose eq1226 eq3725
    | (have j0 := eq3725 X0 x
       have j1 := eq1226 X0 X0 x
       grind)
    | exact resolve eq3725 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq3725
  have eq3757 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3731
  have eq3776 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq3757
  have eq3809 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3776 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq3937 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3809 (σ X0)
       grind)
    | exact superpose eq3809 eq15
    | exact resolve eq15 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3946 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45 X0 X0
       have i₂ := eq3809 (τ X0)
       grind)
    | exact superpose eq3809 eq45
    | exact resolve eq45 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3993 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3946 X0
       have i₂ := eq3809 X0
       grind)
    | exact superpose eq3809 eq3946
    | exact resolve eq3946 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3946
  have eq4001 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3937 X0
       have i₂ := eq3809 X0
       grind)
    | exact superpose eq3809 eq3937
    | exact resolve eq3937 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937
  have eq4372 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq4393 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4372 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq4372
    | exact resolve eq4372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4372
  have eq4417 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq4393
  have eq97727 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2771 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771
  have eq97728 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq97727 X0 X1 X2
       have j1 := eq170 X0 X1 X2
       grind)
    | (have r₁ := eq97727 X0 X1 X2
       have r₂ := eq170 X0 X1 X2
       grind)
    | exact resolve eq97727 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq97727
  have eq97989 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97728 X0 X1 X2
       have i₂ := eq4001 X2
       grind)
    | exact superpose eq4001 eq97728
    | (have j0 := eq97728 X0 X1 X2
       grind)
    | exact resolve eq97728 eq4001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97728
  have eq514193 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (σ X2) (k X0 (σ (τ X1)))) ∨ (k X0 (σ (τ X1))) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97989 X0 (τ X1) X2
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq97989
    | (have j0 := eq97989 X0 (τ X1) X2
       grind)
    | exact resolve eq97989 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq97989
  have eq515041 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (σ X2) (k X0 X1)) ∨ (k X0 (σ (τ X1))) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq514193 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq514193
    | (have j0 := eq514193 X0 X1 X2
       grind)
    | exact resolve eq514193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514193
  have eq515226 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) ∨ (k X0 (σ (τ X1))) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq515041 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq515041
    | (have j0 := eq515041 X0 X1 X2
       grind)
    | exact resolve eq515041 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515041
  have eq515352 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) ∨ (k X0 X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq515226 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq515226
    | (have j0 := eq515226 X0 X1 X2
       grind)
    | exact resolve eq515226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515226
  have eq515900 : ∀ X0 X1 X2 : G, (M.op X0 (k X1 X2)) = (k (k X1 X2) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq515352 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq515352
    | (have j0 := eq515352 X1 X2 (τ X0)
       grind)
    | exact resolve eq515352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515352
  have eq516303 : ∀ X0 X1 X2 : G, (k X1 X2) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 (k X1 X2)) = (k (k X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq515900 X0 X1 X2
       have i₂ := eq3993 X0
       grind)
    | exact superpose eq3993 eq515900
    | (have j0 := eq515900 X0 X1 X2
       grind)
    | exact resolve eq515900 eq3993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3993 eq515900
  have eq516416 : ∀ X0 X1 X2 : G, (M.op X0 (k X1 X2)) = (k (k X1 X2) X0) ∨ (M.op X0 X0) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq516303 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq516303
    | (have j0 := eq516303 X0 X1 X2
       grind)
    | exact resolve eq516303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516303
  have eq516628 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq516416 X0 X0 X0
       have i₂ := eq3809 X0
       grind)
    | exact superpose eq3809 eq516416
    | exact resolve eq516416 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809 eq516416
  have eq523833 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq516628 (M.op x x) X1
       have i₂ := eq20 x x x
       grind)
    | exact superpose eq20 eq516628
    | exact resolve eq516628 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq516628
  have eq525219 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq523833 (σ X1) (σ X0)
       grind)
    | exact superpose eq523833 eq15
    | (have j1 := eq523833 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq523833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525242 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq523833 (τ X1) X0
       grind)
    | exact superpose eq523833 eq18
    | (have j1 := eq523833 (τ X1) X0
       grind)
    | exact resolve eq18 eq523833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq523833
  have eq525529 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq525219 X0 X1
       have i₂ := eq4001 X0
       grind)
    | exact superpose eq4001 eq525219
    | (have j0 := eq525219 X0 X1
       grind)
    | exact resolve eq525219 eq4001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4001 eq525219
  have eq532658 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq525242 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq525242
    | exact resolve eq525242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525242
  have eq533487 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq532658 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq532658
    | (have j0 := eq532658 X0 X1
       grind)
    | exact resolve eq532658 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532658
  have eq550157 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq525529 x y
       grind)
    | exact superpose eq525529 eq16
    | (have j1 := eq525529 x y
       grind)
    | exact resolve eq16 eq525529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525529
  have eq554751 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq550157
       have i₂ := eq533487 y x
       grind)
    | exact superpose eq533487 eq550157
    | (have j1 := eq533487 y x
       grind)
    | (have r₁ := eq550157
       have r₂ := eq533487 y x
       grind)
    | exact resolve eq550157 eq533487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533487 eq550157
  have eq554754 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq554751
  have eq554832 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq554754
       grind)
    | exact superpose eq554754 eq10
    | exact resolve eq10 eq554754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554754
  have eq555428 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq554832
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq554832
    | exact resolve eq554832 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554832
  have eq555429 : y = (M.op x x) := by grind
  clear eq555428
  have eq557444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4417 x
       have i₂ := eq555429
       grind)
    | exact superpose eq555429 eq4417
    | exact resolve eq4417 eq555429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4417 eq555429
  have eq557890 : False := by grind
  exact eq557890

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq34 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq23
    | exact resolve eq23 eq19
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
  have eq63 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq67 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq69 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq83 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq29
    | exact resolve eq29 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X2) X0
       have i₂ := eq63 X0 X1 X2
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq210 : ∀ X0 X1 X2 X3 : G, (k (k (τ X0) X1) (k X2 (τ X3))) = (τ (k (k X0 (σ X1)) (k (σ X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34 X2 X3 (k X0 (σ X1))
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq34
    | exact resolve eq34 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq300 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq300 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq300
    | (have j0 := eq300 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq300 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq7429 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq7430 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq301 X0 X1
       grind)
    | exact superpose eq301 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq301 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq301 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq301 X0 X0
       grind)
    | exact resolve eq13 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7437 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq301 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq7440 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7430 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7430
  have eq7441 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq7429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7429
  have eq7456 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7440 X0 X1
       have j1 := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq7440 X0 X0
       have r₂ := eq13 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq7440 X0 X1
       have r₂ := eq13 (τ X0) (τ X1)
       grind)
    | exact resolve eq7440 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7440
  have eq7457 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (τ (k (k X0 X0) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7441 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq7441
    | (have j0 := eq7441 X0
       grind)
    | exact resolve eq7441 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7441
  have eq7473 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7456 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq7456
    | (have j0 := eq7456 X0 X1
       grind)
    | exact resolve eq7456 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq7456
  have eq7854 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ (k X0 X0)))) = (τ (k (σ (k X0 X0)) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7457 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq7457
    | (have j0 := eq7457 (σ X0)
       grind)
    | exact resolve eq7457 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7457
  have eq7906 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ (k X0 X0)))) = (k (τ (σ (k X0 X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7854 X0
       have i₂ := eq23 (σ (k X0 X0)) X0
       grind)
    | exact superpose eq23 eq7854
    | (have j0 := eq7854 X0
       grind)
    | exact resolve eq7854 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7854
  have eq7930 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (τ (σ X0)) (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7906 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq7906
    | (have j0 := eq7906 X0
       grind)
    | exact resolve eq7906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7906
  have eq7948 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7930 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7930
    | (have j0 := eq7930 X0
       grind)
    | exact resolve eq7930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7930
  have eq7966 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7948 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7948
    | (have j0 := eq7948 X0
       grind)
    | exact resolve eq7948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7948
  have eq8175 : ∀ X0 : G, (k (τ (k (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq7966 (σ X0)
       grind)
    | exact superpose eq7966 eq23
    | (have j1 := eq7966 (σ X0)
       grind)
    | exact resolve eq23 eq7966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq8267 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = (τ (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8175 x
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq8175
    | (have j0 := eq8175 X0
       grind)
    | exact resolve eq8175 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8175
  have eq8333 : ∀ X0 : G, (k (k X0 X0) X0) = (τ (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8267 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq8267
    | (have j0 := eq8267 X0
       grind)
    | exact resolve eq8267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8267
  have eq9353 : ∀ X0 : G, (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8333 X0
       have i₂ := eq300 X0 X0
       grind)
    | exact superpose eq300 eq8333
    | (have j0 := eq8333 X0
       have j1 := eq300 X0 X0
       grind)
    | exact resolve eq8333 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8333
  have eq9439 : ∀ X0 : G, (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9353
  have eq9447 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9439 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9439
    | (have j0 := eq9439 X0
       grind)
    | exact resolve eq9439 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9439
  have eq10029 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (k (σ (τ (M.op (σ (τ X0)) (σ (τ X0))))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ (M.op (σ (τ X0)) (σ (τ X0))))
       have i₂ := eq9447 (τ X0)
       grind)
    | exact superpose eq9447 eq19
    | (have j1 := eq9447 (τ X0)
       grind)
    | exact resolve eq19 eq9447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9447
  have eq10096 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (k (M.op (σ (τ X0)) (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10029 X0
       have i₂ := eq11 (M.op (σ (τ X0)) (σ (τ X0)))
       grind)
    | exact superpose eq11 eq10029
    | (have j0 := eq10029 X0
       grind)
    | exact resolve eq10029 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10029
  have eq10180 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (k (k (τ X0) (τ X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10096 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10096
    | (have j0 := eq10096 X0
       grind)
    | exact resolve eq10096 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10096
  have eq10243 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10180 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq10180
    | (have j0 := eq10180 X0
       grind)
    | exact resolve eq10180 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq10180
  have eq10304 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10243 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq10243
    | (have j0 := eq10243 X0
       grind)
    | exact resolve eq10243 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10243
  have eq10342 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10304 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10304
    | (have j0 := eq10304 X0
       grind)
    | exact resolve eq10304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10304
  have eq10380 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    grind
  clear eq10342
  have eq10409 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10380 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10380
    | (have j0 := eq10380 X0
       grind)
    | exact resolve eq10380 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10380
  have eq10442 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq10409 eq7966
    | (have j0 := eq7966 X0
       have j1 := eq10409 X0
       grind)
    | exact resolve eq7966 eq10409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7966
  have eq10468 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq10409 X0
       grind)
    | exact superpose eq10409 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq10409 X0
       grind)
    | exact resolve eq14 eq10409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10409
  have eq10562 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq14 eq10468
    | (have j0 := eq10468 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq10468 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10468
  have eq10630 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq14 eq10562
    | (have j0 := eq10562 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq10562 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10562
  have eq10631 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10630 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10630
  have eq10688 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10442 X0
       have i₂ := eq10631 X0
       grind)
    | exact superpose eq10631 eq10442
    | (have j0 := eq10442 X0
       have j1 := eq10631 X0
       grind)
    | exact resolve eq10442 eq10631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10442 eq10631
  have eq10702 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10688 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10688
  have eq10707 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq14 eq10702
    | (have j0 := eq10702 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq10702 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10702
  have eq10708 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10707
  have eq10715 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10708 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq10708
    | (have j0 := eq10708 (σ X0)
       grind)
    | exact resolve eq10708 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10778 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq10708 (σ X0)
       grind)
    | exact superpose eq10708 eq29
    | (have j1 := eq10708 (σ X0)
       grind)
    | exact resolve eq29 eq10708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq10902 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10778 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10778
    | (have j0 := eq10778 X0
       grind)
    | exact resolve eq10778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10778
  have eq11312 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10902 (k X0 X0)
       have i₂ := eq10715 X0
       grind)
    | exact superpose eq10715 eq10902
    | (have j0 := eq10902 X0
       have j1 := eq10715 X0
       grind)
    | exact resolve eq10902 eq10715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10902
  have eq11418 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11312 X0
       have i₂ := eq62 (σ X0) (σ X0) (σ X0)
       grind)
    | (have i₁ := eq11312 X0
       have i₂ := eq62 X0 (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) x
       grind)
    | exact superpose eq62 eq11312
    | (have j0 := eq11312 X0
       grind)
    | exact resolve eq11312 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11312
  have eq11421 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11418 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11418
    | (have j0 := eq11418 X0
       grind)
    | exact resolve eq11418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11418
  have eq11422 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11421 X0
       have i₂ := eq62 (σ X0) (σ X0) (σ X0)
       grind)
    | (have i₁ := eq11421 X0
       have i₂ := eq62 X0 (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) x
       grind)
    | exact superpose eq62 eq11421
    | (have j0 := eq11421 X0
       grind)
    | exact resolve eq11421 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11421
  have eq11423 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq11422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11422
  have eq11441 : ∀ X0 : G, (τ (σ X0)) = (k (k (τ (σ X0)) X0) (k X0 (τ (σ X0)))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq210 (σ X0) X0 X0 (σ X0)
       have i₂ := eq11423 (σ X0)
       grind)
    | exact superpose eq11423 eq210
    | (have j1 := eq11423 (σ X0)
       grind)
    | exact resolve eq210 eq11423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq11451 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (τ X0) X0 (k (τ X0) (τ X0))
       have i₂ := eq11423 (τ X0)
       grind)
    | exact superpose eq11423 eq28
    | (have j1 := eq11423 (τ X0)
       grind)
    | exact resolve eq28 eq11423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11423
  have eq11492 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11451 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq11451
    | (have j0 := eq11451 X0
       grind)
    | exact resolve eq11451 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11451
  have eq11502 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11441 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11441
    | (have j0 := eq11441 X0
       grind)
    | exact resolve eq11441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11441
  have eq11527 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11492 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11492
    | (have j0 := eq11492 X0
       grind)
    | exact resolve eq11492 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11492
  have eq11556 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11527 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11527
    | (have j0 := eq11527 X0
       grind)
    | exact resolve eq11527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11527
  have eq11585 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq10708 eq11556
    | (have j0 := eq11556 X0
       have j1 := eq10708 X0
       grind)
    | exact resolve eq11556 eq10708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11556
  have eq12411 : ∀ X0 : G, (τ (M.op (σ (σ X0)) (σ (σ X0)))) = (k (τ (σ (σ X0))) (σ X0)) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq69 (σ X0)
       have i₂ := eq11502 X0
       grind)
    | exact superpose eq11502 eq69
    | (have j1 := eq11502 X0
       grind)
    | exact resolve eq69 eq11502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq12425 : ∀ X0 : G, (k (σ X0) (σ X0)) = (τ (M.op (σ (σ X0)) (σ (σ X0)))) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12411 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq12411
    | (have j0 := eq12411 X0
       grind)
    | exact resolve eq12411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12411
  have eq12431 : ∀ X0 : G, (σ (k X0 X0)) = (τ (M.op (σ (σ X0)) (σ (σ X0)))) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12425 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq12425
    | (have j0 := eq12425 X0
       grind)
    | exact resolve eq12425 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12425
  have eq12436 : ∀ X0 : G, (σ (k X0 X0)) = (τ (σ (σ X0))) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq11502 eq12431
    | (have j0 := eq12431 X0
       have j1 := eq11502 X0
       grind)
    | exact resolve eq12431 eq11502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11502 eq12431
  have eq12438 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12436 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq12436
    | (have j0 := eq12436 X0
       grind)
    | exact resolve eq12436 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12436
  have eq12468 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (τ X0) X0 (k (τ X0) (τ X0))
       have i₂ := eq12438 (τ X0)
       grind)
    | exact superpose eq12438 eq28
    | (have j1 := eq12438 (τ X0)
       grind)
    | exact resolve eq28 eq12438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12438
  have eq12508 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12468 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq12468
    | (have j0 := eq12468 X0
       grind)
    | exact resolve eq12468 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12468
  have eq12542 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12508 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12508
    | (have j0 := eq12508 X0
       grind)
    | exact resolve eq12508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12508
  have eq12575 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12542 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq12542
    | (have j0 := eq12542 X0
       grind)
    | exact resolve eq12542 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq12542
  have eq12604 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12575 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12575
    | (have j0 := eq12575 X0
       grind)
    | exact resolve eq12575 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12575
  have eq12652 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12604 X0
       have i₂ := eq10708 (k X0 X0)
       grind)
    | exact superpose eq10708 eq12604
    | (have j0 := eq12604 X0
       have j1 := eq10708 (k X0 X0)
       grind)
    | exact resolve eq12604 eq10708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10708
  have eq17544 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq339 x y
       grind)
    | exact superpose eq339 eq16
    | (have j1 := eq339 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq339 x y
       grind)
    | exact resolve eq16 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq17592 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq17544
  have eq22041 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7437 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7437
    | (have j0 := eq7437 (σ X1) (σ X0)
       grind)
    | exact resolve eq7437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7437
  have eq22137 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22041 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq22041
    | (have j0 := eq22041 X0 X1
       grind)
    | exact resolve eq22041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22041
  have eq22173 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22137 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq22137
    | (have j0 := eq22137 X0 X1
       grind)
    | exact resolve eq22137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22137
  have eq22208 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22173 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22173
    | (have j0 := eq22173 X0 X1
       grind)
    | exact resolve eq22173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22173
  have eq22241 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22208 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22208
    | (have j0 := eq22208 X0 X1
       grind)
    | exact resolve eq22208 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22208
  have eq22267 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22241 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22241
    | (have j0 := eq22241 X0 X1
       grind)
    | exact resolve eq22241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22241
  have eq22288 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22267 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22267
    | (have j0 := eq22267 X0 X1
       grind)
    | exact resolve eq22267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22267
  have eq22329 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22288 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq22288
    | (have j0 := eq22288 (σ X0) (σ X1)
       grind)
    | exact resolve eq22288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22288
  have eq32810 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7473 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7473
    | (have j0 := eq7473 (σ (k X0 X1)) (σ X1)
       grind)
    | exact resolve eq7473 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7473
  have eq32915 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32810 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq32810
    | (have j0 := eq32810 X0 X1
       grind)
    | exact resolve eq32810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32810
  have eq32959 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32915 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq32915
    | (have j0 := eq32915 X0 X1
       grind)
    | exact resolve eq32915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32915
  have eq32996 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32959 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32959
    | (have j0 := eq32959 X0 X1
       grind)
    | exact resolve eq32959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32959
  have eq33028 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32996 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq32996
    | (have j0 := eq32996 X0 X1
       grind)
    | exact resolve eq32996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32996
  have eq33054 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33028 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33028
    | (have j0 := eq33028 X0 X1
       grind)
    | exact resolve eq33028 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33028
  have eq33080 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33054 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33054
    | (have j0 := eq33054 X0 X1
       grind)
    | exact resolve eq33054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33054
  have eq33118 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33080 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq33080
    | (have j0 := eq33080 (σ (k X0 X1)) (σ X1)
       grind)
    | exact resolve eq33080 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34592 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq17592
  have eq34626 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34592
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq34592
    | exact resolve eq34592 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34592
  have eq34643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq34626
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq34626 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34626
  have eq34651 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq34643
       have r₂ := eq16
       grind)
    | exact resolve eq34643 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34643
  have eq34659 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq62 X0 (σ x) (σ y)
       have i₂ := eq34651
       grind)
    | exact superpose eq34651 eq62
    | exact resolve eq62 eq34651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34673 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34659 (M.op x (σ x))
       have i₂ := eq34659 x
       grind)
    | exact superpose eq34659 eq34659
    | exact resolve eq34659 eq34659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34659
  have eq34688 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq34673
  have eq34695 : (τ (M.op (σ x) (σ x))) = (k x (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq34688
       grind)
    | exact superpose eq34688 eq83
    | exact resolve eq83 eq34688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq34718 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34695
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34695
    | exact resolve eq34695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34695
  have eq34725 : (k x x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34688 eq34718
    | exact resolve eq34718 eq34688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34718
  have eq34727 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq34725
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34725
    | exact resolve eq34725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34725
  have eq34743 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x
       have i₂ := eq34727
       grind)
    | exact superpose eq34727 eq62
    | exact resolve eq62 eq34727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34767 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq34743 x
       have i₂ := eq34727
       grind)
    | exact superpose eq34727 eq34743
    | exact resolve eq34743 eq34727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34743
  have eq34776 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq34767
  have eq34820 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq33080 x x
       have i₂ := eq34776
       grind)
    | exact superpose eq34776 eq33080
    | (have j0 := eq33080 x x
       grind)
    | (have r₁ := eq33080 x x
       have r₂ := eq34776
       grind)
    | exact resolve eq33080 eq34776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33080
  have eq34821 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq33118 x x
       have i₂ := eq34776
       grind)
    | exact superpose eq34776 eq33118
    | (have j0 := eq33118 x x
       grind)
    | exact resolve eq33118 eq34776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33118 eq34776
  have eq34822 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq34821
  have eq34823 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq34822
  have eq34824 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq34820
  have eq34825 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq34824
  have eq34874 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq67 y
       have i₂ := eq34825
       grind)
    | exact superpose eq34825 eq67
    | exact resolve eq67 eq34825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34887 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq62 X0 y y
       have i₂ := eq34825
       grind)
    | exact superpose eq34825 eq62
    | exact resolve eq62 eq34825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34948 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq300 y x
       have i₂ := eq34874
       grind)
    | exact superpose eq34874 eq300
    | (have j0 := eq300 y x
       grind)
    | exact resolve eq300 eq34874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq34874
  have eq34958 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq34948
       have r₂ := eq16
       grind)
    | exact resolve eq34948 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34948
  have eq34959 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq34651 eq34958
    | exact resolve eq34958 eq34651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34651 eq34958
  have eq34961 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq34887 y
       have i₂ := eq34825
       grind)
    | exact superpose eq34825 eq34887
    | exact resolve eq34887 eq34825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34887
  have eq34972 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq34961
  have eq34985 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11585 x
       have i₂ := eq34972
       grind)
    | exact superpose eq34972 eq11585
    | (have j0 := eq11585 x
       grind)
    | exact resolve eq11585 eq34972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34998 : x ≠ y ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq34972
  have eq35011 : x = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq34985
       have r₂ := eq34998
       grind)
    | exact resolve eq34985 eq34998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34985
  have eq35048 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12604 y
       have i₂ := eq35011
       grind)
    | exact superpose eq35011 eq12604
    | exact resolve eq12604 eq35011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35011
  have eq35131 : y = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq35048
       have r₂ := eq34998
       grind)
    | exact resolve eq35048 eq34998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35048
  have eq35161 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10715 x
       have i₂ := eq35131
       grind)
    | exact superpose eq35131 eq10715
    | (have j0 := eq10715 x
       grind)
    | exact resolve eq10715 eq35131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10715
  have eq35234 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq34688 eq35161
    | exact resolve eq35161 eq34688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34688 eq35161
  have eq35308 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq62 (σ x) (σ x) X0
       have i₂ := eq34823
       grind)
    | exact superpose eq34823 eq62
    | exact resolve eq62 eq34823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35967 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq35234
  have eq37196 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq35308 (σ x)
       have i₂ := eq34959
       grind)
    | exact superpose eq34959 eq35308
    | exact resolve eq35308 eq34959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34959 eq35308
  have eq37234 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq37196
  have eq37287 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq37234
       grind)
    | exact superpose eq37234 eq16
    | exact resolve eq16 eq37234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37294 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq37234
       grind)
    | exact superpose eq37234 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq37234
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq37234
       grind)
    | exact resolve eq13 eq37234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37234
  have eq37302 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq37294
  have eq37308 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq37302
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq37302
    | exact resolve eq37302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37302
  have eq37312 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq34823 eq37308
    | exact resolve eq37308 eq34823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37308
  have eq37314 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq34823 eq37312
    | exact resolve eq37312 eq34823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34823 eq37312
  have eq37456 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq35967
  have eq38218 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq37314
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq37314
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq37314 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37314
  have eq38322 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq38218
  have eq38402 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq38322
       have r₂ := eq37287
       grind)
    | exact resolve eq38322 eq37287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37287 eq38322
  have eq38410 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq34825 eq38402
    | exact resolve eq38402 eq34825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34825 eq38402
  have eq38411 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38410
  have eq38428 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67 y
       have i₂ := eq38411
       grind)
    | exact superpose eq38411 eq67
    | exact resolve eq67 eq38411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38434 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11585 y
       have i₂ := eq38411
       grind)
    | exact superpose eq38411 eq11585
    | exact resolve eq11585 eq38411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11585 eq38411
  have eq38453 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq38434
  have eq38495 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12604 x
       have i₂ := eq38453
       grind)
    | exact superpose eq38453 eq12604
    | exact resolve eq12604 eq38453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38453
  have eq38548 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq38495
  have eq39608 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq67 (k X0 X0)
       have i₂ := eq12652 X0
       grind)
    | exact superpose eq12652 eq67
    | (have j1 := eq12652 X0
       grind)
    | exact resolve eq67 eq12652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12652
  have eq39631 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq12604 eq39608
    | (have j0 := eq39608 X0
       have j1 := eq12604 X0
       grind)
    | exact resolve eq39608 eq12604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39608
  have eq39632 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq39631 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39631
  have eq39765 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39632 (k X0 X0)
       have i₂ := eq12604 X0
       grind)
    | exact superpose eq12604 eq39632
    | (have j0 := eq39632 X0
       have j1 := eq12604 X0
       grind)
    | exact resolve eq39632 eq12604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12604 eq39632
  have eq39811 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq39765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39765
  have eq39891 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39811 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq39811
    | exact resolve eq39811 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40149 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq39811 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39811
  have eq40606 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40149 (σ x)
       have i₂ := eq37456
       grind)
    | exact superpose eq37456 eq40149
    | (have j0 := eq40149 (σ x)
       grind)
    | (have r₁ := eq40149 (σ x)
       have r₂ := eq37456
       grind)
    | exact resolve eq40149 eq37456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37456
  have eq40623 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq40149 x
       have i₂ := eq34727
       grind)
    | exact superpose eq34727 eq40149
    | (have j0 := eq40149 x
       grind)
    | exact resolve eq40149 eq34727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34727
  have eq40626 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq40623
  have eq40658 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have j1 := eq40149 (σ x)
       grind)
    | (have r₁ := eq40606
       have r₂ := eq40149 (σ x)
       grind)
    | exact resolve eq40606 eq40149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40149 eq40606
  have eq40680 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40658
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq40658
    | exact resolve eq40658 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40658
  have eq41302 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39891 y
       have i₂ := eq38548
       grind)
    | exact superpose eq38548 eq39891
    | exact resolve eq39891 eq38548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38548 eq39891
  have eq41451 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq41302
  have eq48530 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67 (σ y)
       have i₂ := eq41451
       grind)
    | exact superpose eq41451 eq67
    | exact resolve eq67 eq41451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq41451
  have eq48592 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48530
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq48530
    | exact resolve eq48530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48530
  have eq48620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq38428 eq48592
    | exact resolve eq48592 eq38428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38428 eq48592
  have eq48631 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48620
       have r₂ := eq16
       grind)
    | exact resolve eq48620 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48620
  have eq48636 : (σ x) = (σ (k x x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq40680
       have r₂ := eq48631
       grind)
    | exact resolve eq40680 eq48631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40680
  have eq48639 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq62 x y X0
       have i₂ := eq48631
       grind)
    | exact superpose eq48631 eq62
    | exact resolve eq62 eq48631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48665 : (k x x) = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq48636
       grind)
    | exact superpose eq48636 eq10
    | exact resolve eq10 eq48636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48636
  have eq48866 : x = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48665
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq48665
    | exact resolve eq48665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48665
  have eq48882 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq48866
       have r₂ := eq40626
       grind)
    | exact resolve eq48866 eq40626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40626 eq48866
  have eq48904 : x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq48882 eq35131
    | exact resolve eq35131 eq48882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35131 eq48882
  have eq49010 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq48904
       have r₂ := eq34998
       grind)
    | exact resolve eq48904 eq34998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34998 eq48904
  have eq49025 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq62 X0 x y
       have i₂ := eq49010
       grind)
    | exact superpose eq49010 eq62
    | exact resolve eq62 eq49010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq49010
  have eq49040 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq49025 (M.op x x)
       have i₂ := eq49025 x
       grind)
    | exact superpose eq49025 eq49025
    | exact resolve eq49025 eq49025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49025
  have eq49050 : x = (M.op x x) := by grind
  clear eq49040
  have eq49053 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq340 x
       have i₂ := eq49050
       grind)
    | exact superpose eq49050 eq340
    | (have j0 := eq340 x
       grind)
    | exact resolve eq340 eq49050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq49064 : ∀ X0 : G, x ≠ x ∨ x = (M.op x X0) ∨ x = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq182 x x x
       have i₂ := eq49050
       grind)
    | exact superpose eq49050 eq182
    | (have r₁ := eq182 x x x
       have r₂ := eq49050
       grind)
    | exact resolve eq182 eq49050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq49065 : ∀ X0 : G, x = (k (M.op x X0) x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq49064 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49064
  have eq49072 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq49053
  have eq49076 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq49072
       have i₂ := eq49050
       grind)
    | exact superpose eq49050 eq49072
    | exact resolve eq49072 eq49050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49072
  have eq49077 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq49076
  have eq51618 : x = (k y x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49065 (M.op y x)
       have i₂ := eq48639 x
       grind)
    | exact superpose eq48639 eq49065
    | exact resolve eq49065 eq48639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48639 eq49065
  have eq51627 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51618
  have eq51634 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22329 y x
       have i₂ := eq51627
       grind)
    | exact superpose eq51627 eq22329
    | (have j0 := eq22329 y x
       grind)
    | exact resolve eq22329 eq51627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22329 eq51627
  have eq51639 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51634
  have eq51646 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51639
       have i₂ := eq49077
       grind)
    | exact superpose eq49077 eq51639
    | exact resolve eq51639 eq49077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51639
  have eq51647 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq51646
  have eq52670 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq51647
       grind)
    | exact superpose eq51647 eq16
    | exact resolve eq16 eq51647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51647
  have eq52690 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq48631 eq52670
    | exact resolve eq52670 eq48631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48631 eq52670
  have eq52691 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq52690
  have eq52697 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq52691
       grind)
    | exact superpose eq52691 eq10
    | exact resolve eq10 eq52691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52691
  have eq52888 : x = y ∨ x = y := by
    first
    | (have i₁ := eq52697
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52697
    | exact resolve eq52697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52697
  have eq52889 : x = y := by grind
  clear eq52888
  have eq52902 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52889
       grind)
    | exact superpose eq52889 eq16
    | exact resolve eq16 eq52889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52889
  have eq52903 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq52902
       have i₂ := eq49050
       grind)
    | exact superpose eq49050 eq52902
    | exact resolve eq52902 eq49050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49050 eq52902
  have eq52904 : False := by grind
  exact eq52904

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq37 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X2 X1) ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X2 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq37 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 (k X2 X1) X1 X2
       have r₂ := eq12 X0 (k X2 X1)
       grind)
    | (have r₁ := eq37 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X0)) = X2 ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X2 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq19 X0 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq19 X2 X0 x
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X0)) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq74 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq74 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq74 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq664 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq665 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq664 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq664 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq664 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq1968 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq665 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq2911 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1 (M.op x X0) X1
       have i₂ := eq94 X1 x X0
       grind)
    | exact superpose eq94 eq77
    | (have j1 := eq94 X1 X1 X0
       grind)
    | exact resolve eq77 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq94
  have eq2967 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2911 X0 X1
       have j1 := eq1968 X0 X1
       grind)
    | (have r₁ := eq2911 X0 X1
       have r₂ := eq1968 X0 X1
       grind)
    | (have r₁ := eq2911 X1 X1
       have r₂ := eq1968 X1 X1
       grind)
    | exact resolve eq2911 eq1968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968 eq2911
  have eq3537 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2967 (σ X0) (σ X1)
       grind)
    | exact superpose eq2967 eq15
    | exact resolve eq15 eq2967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3552 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3537 X0 X1
       have i₂ := eq2967 X0 X1
       grind)
    | exact superpose eq2967 eq3537
    | exact resolve eq3537 eq2967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2967 eq3537
  have eq3566 : False := by grind
  exact eq3566

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X0 X0) = X1 ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq42 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq49 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X0 X0) = X1 ∨ (M.op X2 X2) = (k X2 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq35 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq35 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq58 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = (k X2 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49 X0 X1 X2
       have j1 := eq44 (M.op X2 X2) X0
       grind)
    | (have r₁ := eq49 X1 X0 X2
       have r₂ := eq44 X0 X1
       grind)
    | (have r₁ := eq49 X0 (M.op X1 X1) X2
       have r₂ := eq44 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq49 X0 X1 X1
       have r₂ := eq44 (k X1 X1) X1
       grind)
    | exact resolve eq49 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq49
  have eq75 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X0)) = X2 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X2 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq19 X0 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq19 X2 X0 x
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq93 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X0)) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq75 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq75 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq75 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq224 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1834 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq2772 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1 (M.op x X0) X1
       have i₂ := eq93 X1 x X0
       grind)
    | exact superpose eq93 eq77
    | (have j1 := eq93 X1 X1 X0
       grind)
    | exact resolve eq77 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq93
  have eq2827 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2772 X0 X1
       have j1 := eq1834 X1 X0
       grind)
    | (have r₁ := eq2772 X0 X0
       have r₂ := eq1834 X0 X0
       grind)
    | (have r₁ := eq2772 X1 X0
       have r₂ := eq1834 X0 X1
       grind)
    | exact resolve eq2772 eq1834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834 eq2772
  have eq3927 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2827 (σ X0) (σ X1)
       grind)
    | exact superpose eq2827 eq15
    | exact resolve eq15 eq2827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3942 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3927 X0 X1
       have i₂ := eq2827 X0 X1
       grind)
    | exact superpose eq2827 eq3927
    | exact resolve eq3927 eq2827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2827 eq3927
  have eq3956 : False := by grind
  exact eq3956
