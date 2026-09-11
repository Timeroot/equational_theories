import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
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
  have eq77 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq78
    | (have j0 := eq78 (σ X0) (σ X1)
       grind)
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq78
    | (have j0 := eq78 (σ y) (σ X0)
       grind)
    | exact resolve eq78 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq44
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq44 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq131 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq142 : (k (σ (M.op x y)) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq131
       have i₂ := eq78 sF0 y
       grind)
    | exact superpose eq78 eq131
    | (have j1 := eq78 (M.op x y) y
       grind)
    | exact resolve eq131 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq78 (σ X0) sF3
       grind)
    | exact superpose eq78 eq40
    | (have j1 := eq78 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq205 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq78 (σ X0) sF1
       grind)
    | exact superpose eq78 eq41
    | (have j1 := eq78 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq207 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
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
  have eq208 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq208 eq14
    | exact resolve eq14 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq248 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
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
  have eq249 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
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
  have eq258 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (k (M.op y X0) (M.op x y)) = (M.op (M.op y X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq248 eq13
    | (have j0 := eq13 (M.op y X0) (M.op x y)
       grind)
    | exact resolve eq13 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq248 eq52
    | exact resolve eq52 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq78 (τ X0) X1
       grind)
    | exact superpose eq78 eq34
    | (have j1 := eq78 (τ X0) X1
       grind)
    | exact resolve eq34 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq393 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq38
  have eq637 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq94 X1 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq52
    | (have j1 := eq94 X0 X1
       grind)
    | exact resolve eq52 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (σ X0) (σ X1) X2
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq52
    | (have j1 := eq94 X0 X1
       grind)
    | exact resolve eq52 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq649 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq637
    | (have j0 := eq637 X0 X1
       grind)
    | exact resolve eq637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq770 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq393 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq393
    | (have j0 := eq393 y X0
       grind)
    | exact resolve eq393 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq112 eq78
    | (have j0 := eq78 (σ x) (σ y)
       grind)
    | exact resolve eq78 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq935
    | exact resolve eq935 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq939 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq936
       have r₂ := eq27
       grind)
    | exact resolve eq936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq941 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq939 eq249
    | exact resolve eq249 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq939 eq258
    | exact resolve eq258 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq943 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq939 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq939
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq939
       grind)
    | exact resolve eq12 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq939 eq51
    | exact resolve eq51 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq949 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq939 eq52
    | exact resolve eq52 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq939 eq52
    | exact resolve eq52 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq939 eq53
    | exact resolve eq53 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq958 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq943
  have eq1001 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq942 eq249
    | exact resolve eq249 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq942
  have eq1026 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ X0 ∨ (k X0 (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq220 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq1080 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq941 eq948
    | exact resolve eq948 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : (σ y) ≠ (σ y) ∨ (k (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq948 eq13
    | (have j0 := eq13 (σ y) (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq948
       grind)
    | exact resolve eq13 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1097 : (k (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq1084
  have eq1099 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1080
  have eq1102 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1099 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1099
       grind)
    | exact resolve eq13 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1102
  have eq1118 : (τ (σ y)) = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1116 eq88
    | exact resolve eq88 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1122 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq1118
    | exact resolve eq1118 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1125 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq78 y y
       have i₂ := eq1122
       grind)
    | exact superpose eq1122 eq78
    | (have j0 := eq78 y y
       grind)
    | exact resolve eq78 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1122
  have eq1126 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq1125
  have eq1156 : y = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq248 y
       have i₂ := eq1126
       grind)
    | exact superpose eq1126 eq248
    | exact resolve eq248 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1160 : y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq50 y y
       have i₂ := eq1126
       grind)
    | exact superpose eq1126 eq50
    | exact resolve eq50 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1126
  have eq1207 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq949 eq13
    | (have j0 := eq13 (σ y) (M.op X0 (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op X0 (σ y))
       have r₂ := eq949 X0
       grind)
    | exact resolve eq13 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq1220 : ∀ X0 : G, (k (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1207 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1432 : y ≠ y ∨ (k y (M.op (M.op x y) y)) = (M.op y (M.op (M.op x y) y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1160 eq13
    | (have j0 := eq13 y (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 y (M.op (M.op x y) y)
       have r₂ := eq1160
       grind)
    | exact resolve eq13 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1446 : (k y (M.op (M.op x y) y)) = (M.op y (M.op (M.op x y) y)) ∨ y = (M.op y x) := by grind
  clear eq1432
  have eq1590 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq958 eq112
    | exact resolve eq112 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1593 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1590
  have eq1595 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1593 eq950
    | exact resolve eq950 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950 eq1593
  have eq1612 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1595
  have eq2359 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq941 eq1097
    | exact resolve eq1097 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq2360 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq2359
  have eq2399 : ∀ X0 X1 : G, (σ (k X0 y)) = (M.op (σ X0) (M.op (σ (k X0 y)) X1)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq188 eq53
    | (have j1 := eq188 X0
       grind)
    | exact resolve eq53 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq2417 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2360 eq88
    | exact resolve eq88 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2440 : (k y (k y y)) = (τ (k (σ y) (M.op (σ y) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2417 eq770
    | exact resolve eq770 eq2417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq2417
  have eq2503 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (k X0 (M.op x y))) (M.op (σ (M.op x y)) X1)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq205 eq52
    | (have j1 := eq205 X0
       grind)
    | exact resolve eq52 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq205
  have eq2551 : (k y y) = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1156 eq1446
    | exact resolve eq1446 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq2552 : (k y y) = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq2551
  have eq2555 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq2552
       grind)
    | exact superpose eq2552 eq76
    | exact resolve eq76 eq2552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq3062 : (k y (k y y)) = (τ (k (σ y) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1099 eq2440
    | exact resolve eq2440 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq3065 : (σ (k y (k y y))) = (k (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2440 eq15
    | exact resolve eq15 eq2440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2440
  have eq3087 : (k y (k y y)) = (τ (k (σ y) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq3062
  have eq3088 : (k y y) = (k y (k y y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq88 eq3087
    | exact resolve eq3087 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq3087
  have eq3362 : (σ (k y y)) = (k (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3065
       have i₂ := eq3088
       grind)
    | exact superpose eq3088 eq3065
    | exact resolve eq3065 eq3088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065 eq3088
  have eq3388 : (σ (k y y)) = (k (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq3362
  have eq3391 : (k (σ y) (σ y)) = (k (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3388
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq3388
    | exact resolve eq3388 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq3388
  have eq3396 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3391 eq1220
    | exact resolve eq1220 eq3391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq3391
  have eq3398 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq3396
  have eq3405 : (σ y) = (M.op (σ y) (k (σ y) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3398 eq951
    | exact resolve eq951 eq3398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq3398
  have eq3423 : (σ y) = (M.op (σ y) (k (σ y) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq3405
  have eq3850 : ∀ X0 X1 : G, (σ (k y X0)) = (M.op (σ y) (M.op (σ (k y X0)) X1)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq96 eq53
    | (have j1 := eq96 X0
       grind)
    | exact resolve eq53 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq96
  have eq4115 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op (M.op x y) X0)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq30 eq355
    | exact resolve eq355 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq4151 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (M.op (M.op x y) X0)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq37 eq4115
    | (have j0 := eq4115 X0
       grind)
    | exact resolve eq4115 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4115
  have eq6227 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq131 eq642
    | (have j0 := eq642 (M.op x y) y x
       grind)
    | exact resolve eq642 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq642
  have eq6252 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq6227
    | (have j0 := eq6227 X0
       grind)
    | exact resolve eq6227 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6227
  have eq6314 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq20 eq6252
    | (have j0 := eq6252 X0
       grind)
    | exact resolve eq6252 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6252
  have eq6367 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq6314 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6314
    | (have j0 := eq6314 X0
       grind)
    | exact resolve eq6314 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6314
  have eq6690 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq77 eq643
    | (have j0 := eq643 y (M.op x y) x
       grind)
    | exact resolve eq643 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq6771 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq6690
    | (have j0 := eq6690 X0
       grind)
    | exact resolve eq6690 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6690
  have eq6833 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq6771 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6771
    | (have j0 := eq6771 X0
       grind)
    | exact resolve eq6771 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6771
  have eq6886 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq6833
    | (have j0 := eq6833 X0
       grind)
    | exact resolve eq6833 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833
  have eq33132 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1156 eq142
    | exact resolve eq142 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1156
  have eq33190 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq33132
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33132
    | exact resolve eq33132 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33132
  have eq55944 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1612 eq6367
    | exact resolve eq6367 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6367
  have eq55978 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq55944
  have eq55979 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq33190 eq55978
    | exact resolve eq55978 eq33190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33190 eq55978
  have eq56011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq55979
  have eq56012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq26 eq56011
    | exact resolve eq56011 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56011
  have eq56013 : y = (M.op y (M.op x y)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq56012
       have r₂ := eq27
       grind)
    | exact resolve eq56012 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56012
  have eq56022 : (M.op x y) = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq56013 eq289
    | exact resolve eq289 eq56013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq56013
  have eq56065 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2555
       have i₂ := eq56022
       grind)
    | exact superpose eq56022 eq2555
    | exact resolve eq2555 eq56022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555 eq56022
  have eq56290 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq56065
  have eq56330 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq56290
    | exact resolve eq56290 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56290
  have eq57141 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq56330 eq3423
    | exact resolve eq3423 eq56330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3423 eq56330
  have eq57330 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq57141
  have eq59210 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq57330 eq1612
    | exact resolve eq1612 eq57330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612 eq57330
  have eq59261 : y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq59210
  have eq253963 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1001 eq1026
    | exact resolve eq1026 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq1026
  have eq253971 : (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq253963
       have r₂ := eq59261
       grind)
    | exact resolve eq253963 eq59261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59261 eq253963
  have eq253978 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq234 eq253971
    | exact resolve eq253971 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq253971
  have eq253981 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq941 eq253978
    | exact resolve eq253978 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq253978
  have eq253997 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq253981
  have eq254006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq253997 eq112
    | exact resolve eq112 eq253997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq253997
  have eq254025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq254006
  have eq254028 : y = (M.op y x) := by
    first
    | (have r₁ := eq254025
       have r₂ := eq27
       grind)
    | exact resolve eq254025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254025
  have eq254079 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq248 x
       have i₂ := eq254028
       grind)
    | exact superpose eq254028 eq248
    | exact resolve eq248 eq254028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq254087 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq257 y
       have i₂ := eq254028
       grind)
    | exact superpose eq254028 eq257
    | exact resolve eq257 eq254028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq254089 : x ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq254028
       grind)
    | exact superpose eq254028 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq254028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254122 : x ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq254089
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq254089
    | exact resolve eq254089 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254089
  have eq254173 : y = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq254079 eq210
    | exact resolve eq210 eq254079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq254227 : y = (M.op y y) := by
    first
    | exact superpose eq254079 eq254173
    | exact resolve eq254173 eq254079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254173
  have eq255034 : y ≠ y ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq284 y
       have i₂ := eq254227
       grind)
    | exact superpose eq254227 eq284
    | (have r₁ := eq284 y
       have r₂ := eq254227
       grind)
    | exact resolve eq284 eq254227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq255054 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq254227
       grind)
    | exact superpose eq254227 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq254227
       grind)
    | exact resolve eq13 eq254227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255089 : y = (k y y) := by grind
  clear eq255054
  have eq255090 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
  clear eq255034
  have eq255093 : x = (k y (M.op x y)) := by
    first
    | exact superpose eq254087 eq255090
    | exact resolve eq255090 eq254087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255090
  have eq255294 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq649 y y
       have i₂ := eq255089
       grind)
    | exact superpose eq255089 eq649
    | (have j0 := eq649 y y
       grind)
    | exact resolve eq649 eq255089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255089
  have eq255298 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq255294
  have eq255299 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq255298
  have eq255305 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq255299
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq255299
    | exact resolve eq255299 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255299
  have eq255876 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq255093 eq77
    | exact resolve eq77 eq255093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255093
  have eq255959 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq255876
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq255876
    | exact resolve eq255876 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255876
  have eq261754 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op (M.op x y) y)) X0)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4151 eq2399
    | (have j0 := eq2399 (M.op x y) x
       have j1 := eq4151 y
       grind)
    | exact resolve eq2399 eq4151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399 eq4151
  have eq261814 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq254079 eq261754
    | exact resolve eq261754 eq254079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254079 eq261754
  have eq262012 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq261814 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq261814
    | (have j0 := eq261814 X0
       grind)
    | exact resolve eq261814 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261814
  have eq262149 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq262012
    | (have j0 := eq262012 X0
       grind)
    | exact resolve eq262012 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262012
  have eq262221 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq262149
    | (have j0 := eq262149 X0
       grind)
    | exact resolve eq262149 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262149
  have eq262275 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq254087 eq262221
    | (have j0 := eq262221 X0
       grind)
    | exact resolve eq262221 eq254087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254087 eq262221
  have eq270193 : (σ (k y (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2503 eq3850
    | (have j0 := eq3850 (M.op x y) x
       have j1 := eq2503 y x
       grind)
    | exact resolve eq3850 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503 eq3850
  have eq270254 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq77 eq270193
    | exact resolve eq270193 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq270193
  have eq270343 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq255959 eq270254
    | exact resolve eq270254 eq255959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270254
  have eq270381 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq270343
    | exact resolve eq270343 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270343
  have eq270394 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq270381
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq270381
    | exact resolve eq270381 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270381
  have eq270395 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq270394
  have eq605063 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq262275 eq6886
    | exact resolve eq6886 eq262275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6886 eq262275
  have eq605106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq255959 eq605063
    | exact resolve eq605063 eq255959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605063
  have eq605116 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq26 eq605106
    | exact resolve eq605106 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605106
  have eq605118 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq605116
       have r₂ := eq27
       grind)
    | exact resolve eq605116 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605116
  have eq606529 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq605118 eq270395
    | exact resolve eq270395 eq605118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270395 eq605118
  have eq606598 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq606529
  have eq606634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq606598 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq606598
       grind)
    | exact resolve eq12 eq606598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606598
  have eq606672 : (σ (M.op x y)) = (σ y) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq606634
  have eq606683 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq255305 eq606672
    | exact resolve eq606672 eq255305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255305 eq606672
  have eq606690 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq255959 eq606683
    | exact resolve eq606683 eq255959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255959 eq606683
  have eq606691 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq606690
  have eq610670 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq606691 eq29
    | exact resolve eq29 eq606691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606691
  have eq611441 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq610670
    | exact resolve eq610670 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq610670
  have eq611442 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq611441
  have eq611452 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq611442 eq29
    | exact resolve eq29 eq611442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq611442
  have eq612503 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq611452
    | exact resolve eq611452 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq611452
  have eq612577 : x = (M.op (M.op y x) y) ∨ x = y := by
    first
    | exact superpose eq612503 eq207
    | exact resolve eq207 eq612503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq612503
  have eq613207 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq612577
       have i₂ := eq254028
       grind)
    | exact superpose eq254028 eq612577
    | exact resolve eq612577 eq254028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612577
  have eq613303 : x = y ∨ x = y := by
    first
    | (have i₁ := eq613207
       have i₂ := eq254227
       grind)
    | exact superpose eq254227 eq613207
    | exact resolve eq613207 eq254227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254227 eq613207
  have eq613304 : x = y := by grind
  clear eq613303
  have eq613378 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq613304
       grind)
    | exact superpose eq613304 eq18
    | exact resolve eq18 eq613304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq613379 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq613304
       grind)
    | exact superpose eq613304 eq24
    | exact resolve eq24 eq613304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq614104 : x = (M.op x x) := by
    first
    | (have i₁ := eq254028
       have i₂ := eq613304
       grind)
    | exact superpose eq613304 eq254028
    | exact resolve eq254028 eq613304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254028
  have eq614115 : x ≠ x ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq254122
       have i₂ := eq613304
       grind)
    | exact superpose eq613304 eq254122
    | (have r₁ := eq254122
       have r₂ := eq613304
       grind)
    | exact resolve eq254122 eq613304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254122 eq613304
  have eq614187 : (M.op x y) = (k x x) := by grind
  clear eq614115
  have eq614465 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq613379
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq613379
    | exact resolve eq613379 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613379
  have eq614563 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq614465 eq26
    | exact resolve eq26 eq614465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq614465
  have eq615442 : x = (M.op x y) := by
    first
    | (have i₁ := eq614104
       have i₂ := eq613378
       grind)
    | exact superpose eq613378 eq614104
    | exact resolve eq614104 eq613378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613378 eq614104
  have eq615444 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq615442 eq20
    | exact resolve eq20 eq615442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq616098 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq615444
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq615444
    | exact resolve eq615444 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615444
  have eq617762 : x = (k x x) := by
    first
    | exact superpose eq615442 eq614187
    | exact resolve eq614187 eq615442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614187 eq615442
  have eq618410 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq649 x x
       have i₂ := eq617762
       grind)
    | exact superpose eq617762 eq649
    | (have j0 := eq649 x x
       grind)
    | exact resolve eq649 eq617762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq617762
  have eq618423 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq618410
  have eq618424 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq618423
  have eq618446 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq618424
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq618424
    | exact resolve eq618424 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq618424
  have eq618512 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq616098 eq618446
    | exact resolve eq618446 eq616098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618446
  have eq618779 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq616098 eq614563
    | exact resolve eq614563 eq616098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614563 eq616098
  have eq624302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq618512 eq618779
    | exact resolve eq618779 eq618512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618512 eq618779
  have eq624303 : False := by grind
  exact eq624303

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq365 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq365 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq365 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq365 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq377 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq366 (σ X0)
       grind)
    | exact superpose eq366 eq15
    | exact resolve eq15 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq366 (τ X0)
       grind)
    | exact superpose eq366 eq31
    | exact resolve eq31 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq390 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq383 X0
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq383
    | exact resolve eq383 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq396 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq377 X0
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq377
    | exact resolve eq377 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq377
  have eq633 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq658 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq396 X1
       grind)
    | exact superpose eq396 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq672 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq2519 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq672
    | (have j0 := eq672 (τ X0) X1
       grind)
    | exact resolve eq672 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq2578 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2519 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2519
    | (have j0 := eq2519 X0 X1
       grind)
    | exact resolve eq2519 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq2594 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2578 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq2578 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq2578 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq2596 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2594 X0 X1
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq2594
    | (have j0 := eq2594 X0 X1
       grind)
    | exact resolve eq2594 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq2598 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2596 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2596
    | (have j0 := eq2596 X0 X1
       grind)
    | exact resolve eq2596 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2596
  have eq2600 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2598 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2598
    | (have j0 := eq2598 X1 (τ X0)
       grind)
    | exact resolve eq2598 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2619 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2598 (σ X1) X0
       grind)
    | exact superpose eq2598 eq15
    | (have j1 := eq2598 (σ X1) X0
       grind)
    | exact resolve eq15 eq2598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq2654 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2619 X0 X1
       have i₂ := eq396 X1
       grind)
    | exact superpose eq396 eq2619
    | (have j0 := eq2619 X0 X1
       grind)
    | exact resolve eq2619 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq2666 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2600 X0 X1
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq2600
    | (have j0 := eq2600 X0 X1
       grind)
    | exact resolve eq2600 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600
  have eq2672 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2666 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2666
    | (have j0 := eq2666 X0 X1
       grind)
    | exact resolve eq2666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2666
  have eq2703 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq2672 X0 (τ X1)
       grind)
    | exact superpose eq2672 eq17
    | (have j1 := eq2672 X0 (τ X1)
       grind)
    | exact resolve eq17 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2672
  have eq2740 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2703 X0 X1
       have i₂ := eq390 X1
       grind)
    | exact superpose eq390 eq2703
    | (have j0 := eq2703 X0 X1
       grind)
    | exact resolve eq2703 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq2703
  have eq3028 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2740 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2740
    | (have j0 := eq2740 X1 (σ X0)
       grind)
    | exact resolve eq2740 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2740
  have eq3106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3028 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3028
    | (have j0 := eq3028 X0 X1
       grind)
    | exact resolve eq3028 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028
  have eq3113 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3106 X0 X1
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq3106
    | (have j0 := eq3106 X0 X1
       grind)
    | exact resolve eq3106 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3106
  have eq3116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3113 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3113
    | (have j0 := eq3113 X0 X1
       grind)
    | exact resolve eq3113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113
  have eq3572 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2654 x y
       grind)
    | exact superpose eq2654 eq16
    | (have j1 := eq2654 x y
       grind)
    | exact resolve eq16 eq2654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654
  have eq3645 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3572
       have i₂ := eq3116 y x
       grind)
    | exact superpose eq3116 eq3572
    | (have j1 := eq3116 x y
       grind)
    | (have r₁ := eq3572
       have r₂ := eq3116 y x
       grind)
    | exact resolve eq3572 eq3116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116 eq3572
  have eq3646 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3645
  have eq3679 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y y
       have i₂ := eq3646
       grind)
    | exact superpose eq3646 eq61
    | exact resolve eq61 eq3646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3680 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq3646
       grind)
    | exact superpose eq3646 eq61
    | exact resolve eq61 eq3646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646
  have eq3700 : (M.op x x) = (M.op y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67 x (M.op x y) x
       have i₂ := eq3679 x
       grind)
    | exact superpose eq3679 eq67
    | exact resolve eq67 eq3679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq3679
  have eq3734 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3680 x
       have i₂ := eq3700
       grind)
    | exact superpose eq3700 eq3680
    | exact resolve eq3680 eq3700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3680 eq3700
  have eq3755 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3734
  have eq3756 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3755
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq3755
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq3755
    | exact resolve eq3755 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3755
  have eq3757 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3756
       grind)
    | exact superpose eq3756 eq16
    | exact resolve eq16 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756
  have eq3758 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq3757
       have r₂ := eq396 x
       grind)
    | exact resolve eq3757 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3757
  have eq3788 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq396 (M.op y y)
       have i₂ := eq3758
       grind)
    | exact superpose eq3758 eq396
    | exact resolve eq396 eq3758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3758
  have eq3829 : (σ (M.op (M.op y y) (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq3788
       have i₂ := eq396 (M.op x x)
       grind)
    | exact superpose eq396 eq3788
    | exact resolve eq3788 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788
  have eq3847 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq3829
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq3829
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq3829
    | exact resolve eq3829 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3829
  have eq3848 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3847
       have i₂ := eq61 y y y
       grind)
    | (have i₁ := eq3847
       have i₂ := eq61 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq61 eq3847
    | exact resolve eq3847 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq3847
  have eq3849 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3848
       grind)
    | exact superpose eq3848 eq16
    | exact resolve eq16 eq3848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3850 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3848
       grind)
    | exact superpose eq3848 eq10
    | exact resolve eq10 eq3848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3848
  have eq3925 : x = y := by
    first
    | (have i₁ := eq3850
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3850
    | exact resolve eq3850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3850
  have eq3926 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3849
       have i₂ := eq396 x
       grind)
    | exact superpose eq396 eq3849
    | exact resolve eq3849 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq3849
  have eq3927 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3926
       have i₂ := eq3925
       grind)
    | exact superpose eq3925 eq3926
    | exact resolve eq3926 eq3925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3925 eq3926
  have eq3928 : False := by grind
  exact eq3928

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq19 X0 x x
       grind)
    | exact superpose eq19 eq12
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq102 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 X0))
       have i₂ := eq25 X0 X1 X2
       grind)
    | exact superpose eq25 eq12
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k X2 (τ X3)))) = (k (k (σ X0) X1) (k (σ X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38 X2 X3 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq38
    | exact resolve eq38 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq447 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op X2 (M.op X0 (τ X1))))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (M.op X2 (M.op X0 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 (M.op X1 (M.op X2 (τ X1))) X1
       have i₂ := eq25 (τ X1) X1 X2
       grind)
    | exact superpose eq25 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3245 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3308 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3245 X0 X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq3245
    | (have j0 := eq3245 X0 X1
       grind)
    | exact resolve eq3245 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3245
  have eq3358 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3308 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308
  have eq3387 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3358 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq3442 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3387 (M.op x x)
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq3387
    | (have j0 := eq3387 X0
       grind)
    | exact resolve eq3387 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3446 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq3387 X0
       grind)
    | exact superpose eq3387 eq12
    | (have j1 := eq3387 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3387 X0
       grind)
    | exact resolve eq12 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387
  have eq3476 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3446 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq3499 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3476 X0
       grind)
    | exact superpose eq3476 eq11
    | (have j1 := eq3476 X0
       grind)
    | exact resolve eq11 eq3476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq3594 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3499 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3499
    | (have j0 := eq3499 X0
       grind)
    | exact resolve eq3499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3499
  have eq3706 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3594 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594
  have eq3938 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq3442 X0
       grind)
    | exact superpose eq3442 eq12
    | (have j1 := eq3442 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3442 X0
       grind)
    | exact resolve eq12 eq3442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3442
  have eq3971 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3938
  have eq4559 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3971 (σ x)
       have i₂ := eq77 x x
       grind)
    | exact superpose eq77 eq3971
    | (have j0 := eq3971 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | exact resolve eq3971 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq3971
  have eq4615 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559
  have eq4664 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4615 X0
       have j1 := eq3706 (σ X0)
       grind)
    | (have r₁ := eq4615 X0
       have r₂ := eq3706 (σ X0)
       grind)
    | exact resolve eq4615 eq3706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3706 eq4615
  have eq4672 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (k X0 X0))) (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4664 X0
       have i₂ := eq32 (σ (k X0 X0)) (k X0 X0)
       grind)
    | exact superpose eq32 eq4664
    | (have j0 := eq4664 X0
       grind)
    | exact resolve eq4664 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4664
  have eq4679 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4672 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq4672
    | (have j0 := eq4672 X0
       grind)
    | exact resolve eq4672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4672
  have eq4686 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4679 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4679
    | (have j0 := eq4679 X0
       grind)
    | exact resolve eq4679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679
  have eq4693 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4686 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4686
    | (have j0 := eq4686 X0
       grind)
    | exact resolve eq4686 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4686
  have eq4810 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq229 (τ X0) X0 (τ X0) X0
       have i₂ := eq4693 (τ X0)
       grind)
    | exact superpose eq4693 eq229
    | (have j1 := eq4693 (τ X0)
       grind)
    | exact resolve eq229 eq4693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq4693
  have eq4839 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4810 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4810
    | (have j0 := eq4810 X0
       grind)
    | exact resolve eq4810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810
  have eq4850 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4839 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4839
    | (have j0 := eq4839 X0
       grind)
    | exact resolve eq4839 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4839
  have eq4859 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4850 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4850
    | (have j0 := eq4850 X0
       grind)
    | exact resolve eq4850 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4850
  have eq4952 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4859 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq4859
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq4859 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq4988 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4952 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952
  have eq5001 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4988 X0
       have j1 := eq34 X0 X0 X0
       grind)
    | (have r₁ := eq4988 X0
       have r₂ := eq34 X0 X0 x
       grind)
    | exact resolve eq4988 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq4988
  have eq5023 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5001 (M.op x x)
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq5001
    | exact resolve eq5001 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5001
  have eq5129 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5023 (σ X0)
       grind)
    | exact superpose eq5023 eq15
    | exact resolve eq15 eq5023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5209 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5129 X0
       have i₂ := eq5023 X0
       grind)
    | exact superpose eq5023 eq5129
    | exact resolve eq5129 eq5023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5023 eq5129
  have eq5604 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) X1 (σ X0)
       have i₂ := eq5209 X0
       grind)
    | exact superpose eq5209 eq25
    | exact resolve eq25 eq5209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq22549 : ∀ X0 X1 X2 : G, (k X1 (τ (σ (M.op X2 (M.op X0 (τ (σ X1))))))) = (τ (σ (M.op X0 (τ (σ X1))))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) ∨ (M.op X0 (τ (σ X1))) = (M.op X2 (M.op X0 (τ (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X1 (σ (M.op X2 (M.op X0 (τ (σ X1)))))
       have i₂ := eq447 X0 (σ X1) X2
       grind)
    | exact superpose eq447 eq40
    | (have j1 := eq447 X0 (σ X1) X2
       grind)
    | exact resolve eq40 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq22600 : ∀ X0 X1 X2 : G, (M.op X0 (τ (σ X1))) = (k X1 (τ (σ (M.op X2 (M.op X0 (τ (σ X1))))))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) ∨ (M.op X0 (τ (σ X1))) = (M.op X2 (M.op X0 (τ (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22549 X0 X1 X2
       have i₂ := eq10 (M.op X0 (τ (σ X1)))
       grind)
    | exact superpose eq10 eq22549
    | (have j0 := eq22549 X0 X1 X2
       grind)
    | exact resolve eq22549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22549
  have eq22663 : ∀ X0 X1 X2 : G, (M.op X0 (τ (σ X1))) = (k X1 (M.op X2 (M.op X0 (τ (σ X1))))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) ∨ (M.op X0 (τ (σ X1))) = (M.op X2 (M.op X0 (τ (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22600 X0 X1 X2
       have i₂ := eq10 (M.op X2 (M.op X0 (τ (σ X1))))
       grind)
    | exact superpose eq10 eq22600
    | (have j0 := eq22600 X0 X1 X2
       grind)
    | exact resolve eq22600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22600
  have eq22696 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 (M.op X2 (M.op X0 X1))) ∨ (τ (σ X1)) = (M.op X0 (τ (σ X1))) ∨ (M.op X0 (τ (σ X1))) = (M.op X2 (M.op X0 (τ (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22663 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22663
    | (have j0 := eq22663 X0 X1 X2
       grind)
    | exact resolve eq22663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22663
  have eq22725 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 (M.op X2 (M.op X0 X1))) ∨ (M.op X0 (τ (σ X1))) = (M.op X2 (M.op X0 (τ (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22696 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22696
    | (have j0 := eq22696 X0 X1 X2
       grind)
    | exact resolve eq22696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22696
  have eq22745 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22725 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22725
    | (have j0 := eq22725 X0 X1 X2
       grind)
    | exact resolve eq22725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22725
  have eq22757 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 (M.op X2 (M.op X0 X1))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq22745 X0 X1 X2
       have j1 := eq102 X0 X1 X2
       grind)
    | (have r₁ := eq22745 X0 X1 X2
       have r₂ := eq102 X0 X1 X2
       grind)
    | (have r₁ := eq22745 X2 (M.op X0 X1) X2
       have r₂ := eq102 X0 X1 X2
       grind)
    | exact resolve eq22745 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq22745
  have eq22768 : ∀ X0 X2 X3 : G, (k (M.op X0 X2) (M.op X3 X0)) = X0 ∨ (M.op X0 X2) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq22757 (M.op X0 x) (M.op x x) X2
       have i₂ := eq19 X0 x x
       grind)
    | exact superpose eq19 eq22757
    | exact resolve eq22757 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22820 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22757 X0 X1 (M.op x X0)
       have i₂ := eq19 x X0 X1
       grind)
    | exact superpose eq19 eq22757
    | (have j0 := eq22757 X0 X1 x
       grind)
    | exact resolve eq22757 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22757
  have eq23015 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq22820 (τ X0) X1
       grind)
    | exact superpose eq22820 eq18
    | (have j1 := eq22820 (τ X0) X1
       grind)
    | exact resolve eq18 eq22820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25038 : ∀ X0 X1 : G, (τ X1) ≠ X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq23015 X0 X1
       grind)
    | exact superpose eq23015 eq12
    | (have j1 := eq23015 X1 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq23015 X0 (τ X0)
       grind)
    | exact resolve eq12 eq23015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25039 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq23015 X0 X1
       grind)
    | exact superpose eq23015 eq13
    | (have j0 := eq13 X0 (τ X1)
       have j1 := eq23015 X1 X0
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq23015 X0 X1
       grind)
    | exact resolve eq13 eq23015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23015
  have eq25091 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq25039 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25039
  have eq25112 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq25038 X0 X1
       have j1 := eq25091 X0 X1
       grind)
    | (have r₁ := eq25038 (k (τ X1) (τ X1)) X1
       have r₂ := eq25091 (τ X1) X1
       grind)
    | (have r₁ := eq25038 X0 X1
       have r₂ := eq25091 X0 X1
       grind)
    | (have r₁ := eq25038 (τ X1) X1
       have r₂ := eq25091 (τ X1) X1
       grind)
    | exact resolve eq25038 eq25091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25038 eq25091
  have eq25825 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25112 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25112
    | exact resolve eq25112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25112
  have eq26011 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25825 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq25825
    | (have j0 := eq25825 X0 X1
       grind)
    | exact resolve eq25825 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25825
  have eq26462 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq26011 X0 X1
       grind)
    | exact superpose eq26011 eq10
    | (have j1 := eq26011 X0 X1
       grind)
    | exact resolve eq10 eq26011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26598 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26462 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq26462
    | (have j0 := eq26462 X0 X1
       grind)
    | exact resolve eq26462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26462
  have eq26689 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq26598 (σ X0) X1
       grind)
    | exact superpose eq26598 eq32
    | (have j1 := eq26598 (σ X0) X1
       grind)
    | exact resolve eq32 eq26598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq26598
  have eq31526 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (σ X1)
       have i₂ := eq26689 X1 (σ X0)
       grind)
    | exact superpose eq26689 eq40
    | (have j1 := eq26689 X1 (σ X0)
       grind)
    | exact resolve eq40 eq26689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq26689
  have eq31601 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31526 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq31526
    | (have j0 := eq31526 X0 X1
       grind)
    | exact resolve eq31526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31526
  have eq31639 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31601 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31601
    | (have j0 := eq31601 X0 X1
       grind)
    | exact resolve eq31601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31601
  have eq31652 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31639 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31639
    | (have j0 := eq31639 X0 X1
       grind)
    | exact resolve eq31639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31639
  have eq32200 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq31652 X0 X1
       grind)
    | exact superpose eq31652 eq11
    | (have j1 := eq31652 X0 X1
       grind)
    | exact resolve eq11 eq31652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31652
  have eq32427 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32200 y x
       grind)
    | exact superpose eq32200 eq16
    | (have j1 := eq32200 y x
       grind)
    | exact resolve eq16 eq32200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32604 : y = (k y x) := by
    first
    | (have j1 := eq26011 x y
       grind)
    | (have r₁ := eq32427
       have r₂ := eq26011 x y
       grind)
    | exact resolve eq32427 eq26011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26011 eq32427
  have eq32945 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22820 x y
       have i₂ := eq32604
       grind)
    | exact superpose eq32604 eq22820
    | (have j0 := eq22820 x y
       grind)
    | exact resolve eq22820 eq32604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22820 eq32604
  have eq32948 : y = (M.op x y) := by grind
  clear eq32945
  have eq32966 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq19 x y X0
       have i₂ := eq32948
       grind)
    | exact superpose eq32948 eq19
    | exact resolve eq19 eq32948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32990 : ∀ X0 : G, x = y ∨ x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq22768 x y x
       have i₂ := eq32948
       grind)
    | exact superpose eq32948 eq22768
    | exact resolve eq22768 eq32948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22768
  have eq33294 : y = (M.op y y) := by
    first
    | (have i₁ := eq32966 (M.op y x)
       have i₂ := eq32966 x
       grind)
    | exact superpose eq32966 eq32966
    | exact resolve eq32966 eq32966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32966
  have eq33607 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5604 y x
       have i₂ := eq33294
       grind)
    | exact superpose eq33294 eq5604
    | exact resolve eq5604 eq33294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5604 eq33294
  have eq34723 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq32990 X0
       grind)
    | exact superpose eq32990 eq16
    | (have j1 := eq32990 X0
       grind)
    | exact resolve eq16 eq32990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32990
  have eq34744 : ∀ X0 : G, x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have j0 := eq34723 X0
       grind)
    | (have r₁ := eq34723 X0
       have r₂ := eq5209 x
       grind)
    | exact resolve eq34723 eq5209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34723
  have eq36189 : ∀ X0 : G, (σ y) = (M.op (σ (k y X0)) (σ y)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq33607 (σ X0)
       have i₂ := eq32200 y X0
       grind)
    | exact superpose eq32200 eq33607
    | (have j1 := eq32200 y X0
       grind)
    | exact resolve eq33607 eq32200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32200 eq33607
  have eq83660 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36189 (M.op x x)
       have i₂ := eq34744 x
       grind)
    | exact superpose eq34744 eq36189
    | exact resolve eq36189 eq34744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34744 eq36189
  have eq83825 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq83660
       grind)
    | exact superpose eq83660 eq16
    | exact resolve eq16 eq83660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83660
  have eq83917 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq83825
       have i₂ := eq32948
       grind)
    | exact superpose eq32948 eq83825
    | exact resolve eq83825 eq32948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32948 eq83825
  have eq83918 : x = y := by grind
  clear eq83917
  have eq84352 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83918
       grind)
    | exact superpose eq83918 eq16
    | exact resolve eq16 eq83918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83918
  have eq84572 : False := by grind
  exact eq84572

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq468 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq468 (σ X0)
       grind)
    | exact superpose eq468 eq15
    | (have j1 := eq468 (σ X0)
       grind)
    | exact resolve eq15 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq468 (τ X0)
       grind)
    | exact superpose eq468 eq18
    | (have j1 := eq468 (τ X0)
       grind)
    | exact resolve eq18 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq468
  have eq491 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq486 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq486
    | (have j0 := eq486 X0
       grind)
    | exact resolve eq486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq525 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq479
  have eq527 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq525 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq525
    | (have j0 := eq525 X0
       grind)
    | exact resolve eq525 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq528 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq537 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq528 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq528
    | exact resolve eq528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ X0) (σ X0)
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq62
    | exact resolve eq62 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq537 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq537
    | exact resolve eq537 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq568 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq565 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq565
    | exact resolve eq565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq585 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq568 (τ X0)
       grind)
    | exact superpose eq568 eq32
    | exact resolve eq32 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq585 X0
       have i₂ := eq568 X0
       grind)
    | exact superpose eq568 eq585
    | exact resolve eq585 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq668 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq14 (τ X1) (τ X0)
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (τ X1) (τ X0)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq675 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq668 X0 X1
       have i₂ := eq592 X1
       grind)
    | exact superpose eq592 eq668
    | (have j0 := eq668 X0 X1
       grind)
    | exact resolve eq668 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq699 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1
       have i₂ := eq592 X0
       grind)
    | exact superpose eq592 eq675
    | (have j0 := eq675 X0 X1
       grind)
    | exact resolve eq675 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq722 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq592 X0
       grind)
    | exact superpose eq592 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq808 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq547 (k X0 X0) (M.op x (σ X0))
       have i₂ := eq547 X0 x
       grind)
    | exact superpose eq547 eq547
    | exact resolve eq547 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq834 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq808 X0
       have i₂ := eq568 (k X0 X0)
       grind)
    | exact superpose eq568 eq808
    | exact resolve eq808 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq844 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq834 X0
       have i₂ := eq568 X0
       grind)
    | exact superpose eq568 eq834
    | exact resolve eq834 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq850 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq844 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq844 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq844
    | exact resolve eq844 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq868 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq879 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq868 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq868
    | exact resolve eq868 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq887 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq879
  have eq76076 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq491 (M.op X0 X0)
       have i₂ := eq722 X0 X1
       grind)
    | (have i₁ := eq491 (M.op X1 X1)
       have i₂ := eq722 X0 X1
       grind)
    | exact superpose eq722 eq491
    | (have j0 := eq491 (M.op X0 X0)
       have j1 := eq722 X1 X0
       grind)
    | exact resolve eq491 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq76264 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (τ (M.op (M.op X1 X1) (M.op X1 X1))) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq592 (M.op X0 X0)
       have i₂ := eq722 X0 X1
       grind)
    | (have i₁ := eq592 (M.op X1 X1)
       have i₂ := eq722 X0 X1
       grind)
    | exact superpose eq722 eq592
    | (have j1 := eq722 X0 X1
       grind)
    | exact resolve eq592 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76330 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq722 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq76396 : ∀ X0 X1 : G, (τ X1) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76264 X0 X1
       have i₂ := eq62 X1 X1 X1
       grind)
    | (have i₁ := eq76264 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq62 eq76264
    | (have j0 := eq76264 X0 X1
       grind)
    | exact resolve eq76264 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76264
  have eq76521 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = (σ (τ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76076 X0 X1
       have i₂ := eq592 (M.op X0 X0)
       grind)
    | exact superpose eq592 eq76076
    | (have j0 := eq76076 X0 X1
       grind)
    | exact resolve eq76076 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76076
  have eq76597 : ∀ X0 X1 : G, (τ X1) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76396 X0 X1
       have i₂ := eq592 (M.op X0 X0)
       grind)
    | exact superpose eq592 eq76396
    | (have j0 := eq76396 X0 X1
       grind)
    | exact resolve eq76396 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76396
  have eq76608 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X1 X1) (M.op X1 X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76521 X0 X1
       have i₂ := eq11 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq76521
    | (have j0 := eq76521 X0 X1
       grind)
    | exact resolve eq76521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76521
  have eq76626 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76597 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq76597 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq76597
    | (have j0 := eq76597 X0 X1
       grind)
    | exact resolve eq76597 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76597
  have eq76634 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76608 X0 X1
       have i₂ := eq568 (M.op X1 X1)
       grind)
    | exact superpose eq568 eq76608
    | (have j0 := eq76608 X0 X1
       grind)
    | exact resolve eq76608 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76608
  have eq76654 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76634 X0 X1
       have i₂ := eq62 X1 X1 X1
       grind)
    | (have i₁ := eq76634 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq62 eq76634
    | (have j0 := eq76634 X0 X1
       grind)
    | exact resolve eq76634 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76634
  have eq76670 : ∀ X0 X1 : G, X0 = X1 ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76654 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq76654 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq76654
    | (have j0 := eq76654 X0 X1
       grind)
    | exact resolve eq76654 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76654
  have eq76681 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ X0 = X1 ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76670 X0 X1
       have i₂ := eq592 (M.op X0 X0)
       grind)
    | exact superpose eq592 eq76670
    | (have j0 := eq76670 X0 X1
       grind)
    | exact resolve eq76670 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq76670
  have eq76687 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ X0 = X1 ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76681 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq76681 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq76681
    | (have j0 := eq76681 X0 X1
       grind)
    | exact resolve eq76681 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq76681
  have eq76690 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq76687 X0 X1
       have j1 := eq76330 X1 X0
       grind)
    | (have r₁ := eq76687 X1 X1
       have r₂ := eq76330 X0 X1
       grind)
    | (have r₁ := eq76687 (τ X1) (τ (M.op X1 X1))
       have r₂ := eq76330 X0 X1
       grind)
    | (have r₁ := eq76687 (τ (M.op X1 X1)) (τ X1)
       have r₂ := eq76330 X0 X1
       grind)
    | exact resolve eq76687 eq76330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76330 eq76687
  have eq76730 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76690 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq76690
    | (have j0 := eq76690 (τ (k (σ X0) X1)) (M.op (τ X1) X0)
       grind)
    | exact resolve eq76690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76690
  have eq77005 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76730 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq76730
    | (have j0 := eq76730 X0 X1
       grind)
    | exact resolve eq76730 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76730
  have eq77431 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq77005 X1 X0
       grind)
    | exact superpose eq77005 eq19
    | (have j1 := eq77005 X1 X0
       grind)
    | exact resolve eq19 eq77005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq77005
  have eq79006 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77431 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77431
    | (have j0 := eq77431 (σ X0) X1
       grind)
    | exact resolve eq77431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77431
  have eq79493 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79006 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq79006
    | (have j0 := eq79006 X0 X1
       grind)
    | exact resolve eq79006 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79006
  have eq79586 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79493 X0 X1
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq79493
    | (have j0 := eq79493 X0 X1
       grind)
    | exact resolve eq79493 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79493
  have eq79655 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79586 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq79586
    | (have j0 := eq79586 X0 X1
       grind)
    | exact resolve eq79586 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79586
  have eq79706 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79655 X0 X1
       have i₂ := eq568 X0
       grind)
    | exact superpose eq568 eq79655
    | (have j0 := eq79655 X0 X1
       grind)
    | exact resolve eq79655 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79655
  have eq82057 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76626 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq76626
    | exact resolve eq76626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76626
  have eq82339 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82057 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq82057
    | (have j0 := eq82057 X0 X1
       grind)
    | exact resolve eq82057 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq82057
  have eq82711 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82339 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82339
    | (have j0 := eq82339 X1 (σ X0)
       grind)
    | exact resolve eq82339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82339
  have eq82899 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82711 X0 X1
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq82711
    | (have j0 := eq82711 X0 X1
       grind)
    | exact resolve eq82711 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82711
  have eq82916 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82899 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq82899
    | (have j0 := eq82899 X0 X1
       grind)
    | exact resolve eq82899 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82899
  have eq82931 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82916 X0 X1
       have i₂ := eq568 X0
       grind)
    | exact superpose eq568 eq82916
    | (have j0 := eq82916 X0 X1
       grind)
    | exact resolve eq82916 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82916
  have eq83194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq82931 (σ X0) (σ X1)
       grind)
    | exact superpose eq82931 eq15
    | (have j1 := eq82931 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq82931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82931
  have eq83318 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83194 X0 X1
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq83194
    | (have j0 := eq83194 X0 X1
       grind)
    | exact resolve eq83194 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq83194
  have eq83418 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83318 X0 X1
       have i₂ := eq568 X0
       grind)
    | exact superpose eq568 eq83318
    | (have j0 := eq83318 X0 X1
       grind)
    | exact resolve eq83318 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq83318
  have eq108170 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83418 x y
       grind)
    | exact superpose eq83418 eq16
    | (have j1 := eq83418 x y
       grind)
    | exact resolve eq16 eq83418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83418
  have eq108652 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq108170
       have i₂ := eq79706 x y
       grind)
    | exact superpose eq79706 eq108170
    | (have j1 := eq79706 x y
       grind)
    | (have r₁ := eq108170
       have r₂ := eq79706 x y
       grind)
    | (have r₁ := eq108170
       have r₂ := eq79706 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq108170
       have r₂ := eq79706 (k y x) (M.op x y)
       grind)
    | exact resolve eq108170 eq79706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79706 eq108170
  have eq108655 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq108652
  have eq108656 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq108655
  have eq108663 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq108656
       grind)
    | exact superpose eq108656 eq10
    | exact resolve eq10 eq108656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108656
  have eq108958 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq108663
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq108663
    | exact resolve eq108663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108663
  have eq109017 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108958
       grind)
    | exact superpose eq108958 eq16
    | exact resolve eq16 eq108958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108958
  have eq109018 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq109017
       have r₂ := eq850 x
       grind)
    | exact resolve eq109017 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq109017
  have eq111831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq887 x
       have i₂ := eq109018
       grind)
    | exact superpose eq109018 eq887
    | exact resolve eq887 eq109018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109018
  have eq112031 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq111831
       have r₂ := eq16
       grind)
    | exact resolve eq111831 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111831
  have eq112086 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq112031
       grind)
    | exact superpose eq112031 eq10
    | exact resolve eq10 eq112031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112031
  have eq112460 : y = (M.op x x) := by
    first
    | (have i₁ := eq112086
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq112086
    | exact resolve eq112086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112086
  have eq112641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq887 x
       have i₂ := eq112460
       grind)
    | exact superpose eq112460 eq887
    | exact resolve eq887 eq112460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq112460
  have eq112841 : False := by grind
  exact eq112841

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq64 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq74 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq344 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq723 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (σ X0) (σ X1) X2
       have i₂ := eq347 X0 X1
       grind)
    | exact superpose eq347 eq63
    | (have j1 := eq347 X0 X1
       grind)
    | exact resolve eq63 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (M.op (σ (k X0 X1)) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (σ X0) (σ X1) x
       have i₂ := eq347 X0 X1
       grind)
    | exact superpose eq347 eq64
    | (have j1 := eq347 X0 X1
       grind)
    | exact resolve eq64 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq731 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq74 (σ x)
       have i₂ := eq347 x x
       grind)
    | exact superpose eq347 eq74
    | (have j1 := eq347 X0 X0
       grind)
    | exact resolve eq74 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq347
  have eq737 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq738 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq742 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq737 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq737
    | (have j0 := eq737 X0
       grind)
    | exact resolve eq737 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq743 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq738 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq738
    | (have j0 := eq738 X0
       grind)
    | exact resolve eq738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq2690 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq742 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq742
    | exact resolve eq742 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2730 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2690 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2690
    | (have j0 := eq2690 X0
       grind)
    | exact resolve eq2690 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2690
  have eq2733 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2730 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2730
    | (have j0 := eq2730 X0
       grind)
    | exact resolve eq2730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq2734 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2733 X0
       have i₂ := eq20 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq20 eq2733
    | (have j0 := eq2733 X0
       grind)
    | exact resolve eq2733 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733
  have eq2735 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2734 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2734
    | (have j0 := eq2734 X0
       grind)
    | exact resolve eq2734 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq2736 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2735 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2735
    | (have j0 := eq2735 X0
       grind)
    | exact resolve eq2735 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq2752 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq2736
  have eq3086 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    grind
  clear eq743
  have eq3088 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3086 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3086
    | (have j0 := eq3086 X0
       grind)
    | exact resolve eq3086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq3147 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq344
    | exact resolve eq344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq3200 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3147 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3147
    | (have j0 := eq3147 X0 X1
       grind)
    | exact resolve eq3147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3147
  have eq3577 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (τ (k X2 (σ (M.op X0 X1)))) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (k X0 X1)
       have i₂ := eq3200 X1 X0
       grind)
    | exact superpose eq3200 eq24
    | (have j1 := eq3200 X1 X0
       grind)
    | exact resolve eq24 eq3200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3582 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (k X0 X1) X2
       have i₂ := eq3200 X1 X0
       grind)
    | exact superpose eq3200 eq30
    | (have j1 := eq3200 X1 X0
       grind)
    | exact resolve eq30 eq3200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3601 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3582 X0 X1 X2
       have i₂ := eq30 (M.op X0 X1) X2
       grind)
    | exact superpose eq30 eq3582
    | (have j0 := eq3582 X0 X1 X2
       grind)
    | exact resolve eq3582 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3582
  have eq3606 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (k (τ X2) (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3577 X0 X1 X2
       have i₂ := eq24 X2 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq3577
    | (have j0 := eq3577 X0 X1 X2
       grind)
    | exact resolve eq3577 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3577
  have eq6896 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X1) = X2 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3601 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3601
    | (have j0 := eq3601 X1 X2 X2
       grind)
    | exact resolve eq3601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3601
  have eq7025 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2752 X0
       have i₂ := eq6896 X0 X0 X0
       grind)
    | exact superpose eq6896 eq2752
    | (have j0 := eq2752 X0
       have j1 := eq6896 X0 X0 X0
       grind)
    | exact resolve eq2752 eq6896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752 eq6896
  have eq7097 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7025 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7025
  have eq7126 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq7097
  have eq7129 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X1) = X2 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3606 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3606
    | (have j0 := eq3606 X1 X2 X2
       grind)
    | exact resolve eq3606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3606
  have eq11580 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq74 (σ X0)
       have i₂ := eq3088 X0
       grind)
    | exact superpose eq3088 eq74
    | (have j1 := eq3088 X0
       grind)
    | exact resolve eq74 eq3088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3088
  have eq11622 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11580 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq11580
    | (have j0 := eq11580 X0
       grind)
    | exact resolve eq11580 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11580
  have eq11623 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq11622 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11622
  have eq11689 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) = (σ (k (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11623 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq11623
    | exact resolve eq11623 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11714 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ X0) (σ (k X0 X0))
       have i₂ := eq11623 X0
       grind)
    | exact superpose eq11623 eq63
    | exact resolve eq63 eq11623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11715 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ (k X0 (k X0 X0))) (M.op (σ (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) (σ (k X0 X0)) X1
       have i₂ := eq11623 X0
       grind)
    | exact superpose eq11623 eq63
    | exact resolve eq63 eq11623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11623
  have eq11757 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) = (k (σ (τ X0)) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11689 X0
       have i₂ := eq20 (k X0 X0) (τ X0)
       grind)
    | exact superpose eq20 eq11689
    | exact resolve eq11689 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11689
  have eq11790 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (σ (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11757 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11757
    | exact resolve eq11757 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11757
  have eq11814 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11790 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq11790
    | exact resolve eq11790 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11790
  have eq11880 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7129 X0 X0 X0
       have i₂ := eq11814 X0
       grind)
    | exact superpose eq11814 eq7129
    | (have j0 := eq7129 X0 X0 X0
       grind)
    | exact resolve eq7129 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7129
  have eq11927 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11880 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11880
  have eq11975 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11927 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq11927
    | (have j0 := eq11927 X0
       grind)
    | exact resolve eq11927 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11927
  have eq12196 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq11714 X0 X1
       have i₂ := eq11814 X0
       grind)
    | exact superpose eq11814 eq11714
    | exact resolve eq11714 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11714
  have eq12607 : ∀ X0 X2 : G, (σ (M.op X0 (k X0 X0))) = (M.op (σ X0) (M.op (σ (M.op X0 (k X0 X0))) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq63 (M.op x (σ X0)) (σ (M.op X0 (k X0 X0))) X2
       have i₂ := eq12196 X0 x
       grind)
    | exact superpose eq12196 eq63
    | exact resolve eq63 eq12196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12196
  have eq12836 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (k X0 X0) X1
       have i₂ := eq11975 X0
       grind)
    | exact superpose eq11975 eq63
    | (have j1 := eq11975 X0
       grind)
    | exact resolve eq63 eq11975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11975
  have eq14013 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ (M.op X0 (k X0 X0))) (M.op (σ (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11715 X0 X1
       have i₂ := eq11814 X0
       grind)
    | exact superpose eq11814 eq11715
    | exact resolve eq11715 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11715 eq11814
  have eq15349 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12607 X0 (M.op (σ (k X0 X0)) x)
       have i₂ := eq14013 X0 x
       grind)
    | exact superpose eq14013 eq12607
    | exact resolve eq12607 eq14013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12607 eq14013
  have eq17971 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12836 X0 X0
       have i₂ := eq7126 X0
       grind)
    | exact superpose eq7126 eq12836
    | (have j0 := eq12836 X0 x
       have j1 := eq7126 X0
       grind)
    | exact resolve eq12836 eq7126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7126 eq12836
  have eq18012 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq17971 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17971
  have eq18015 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq18012 X0
       have i₂ := eq63 X0 (M.op X0 X0) X0
       grind)
    | (have i₁ := eq18012 X0
       have i₂ := eq63 X0 (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) X0)) x
       grind)
    | exact superpose eq63 eq18012
    | (have j0 := eq18012 X0
       grind)
    | exact resolve eq18012 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq18012
  have eq18016 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18015 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18015
  have eq18029 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq18016 X0
       grind)
    | exact superpose eq18016 eq74
    | (have j1 := eq18016 X0
       grind)
    | exact resolve eq74 eq18016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq18016
  have eq18091 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18029 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18029
  have eq18201 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq15349 X0
       have i₂ := eq18091 X0
       grind)
    | exact superpose eq18091 eq15349
    | exact resolve eq15349 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15349
  have eq18238 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq18091 (σ X0)
       grind)
    | exact superpose eq18091 eq15
    | exact resolve eq15 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18245 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq18091 (τ X0)
       grind)
    | exact superpose eq18091 eq33
    | exact resolve eq33 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq18299 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18245 X0
       have i₂ := eq18091 X0
       grind)
    | exact superpose eq18091 eq18245
    | exact resolve eq18245 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18245
  have eq18306 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18238 X0
       have i₂ := eq18091 X0
       grind)
    | exact superpose eq18091 eq18238
    | exact resolve eq18238 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18091 eq18238
  have eq18797 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq723 (τ X0) X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq723
    | (have j0 := eq723 (τ X0) X1 X2
       grind)
    | exact resolve eq723 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq18980 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18797 X0 X1 X2
       have i₂ := eq18306 (τ X0)
       grind)
    | exact superpose eq18306 eq18797
    | (have j0 := eq18797 X0 X1 X2
       grind)
    | exact resolve eq18797 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18797
  have eq19065 : ∀ X0 X1 X2 : G, (σ X1) = (σ (τ (M.op X0 X0))) ∨ (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18980 X0 X1 X2
       have i₂ := eq18299 X0
       grind)
    | exact superpose eq18299 eq18980
    | (have j0 := eq18980 X0 X1 X2
       grind)
    | exact resolve eq18980 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18980
  have eq19137 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ X1) ∨ (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19065 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq19065
    | (have j0 := eq19065 X0 X1 X2
       grind)
    | exact resolve eq19065 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19065
  have eq19199 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19137 X0 X1 X2
       have i₂ := eq18306 X1
       grind)
    | exact superpose eq18306 eq19137
    | (have j0 := eq19137 X0 X1 X2
       grind)
    | exact resolve eq19137 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19137
  have eq19248 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19199 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19199
    | (have j0 := eq19199 X0 X1 X2
       grind)
    | exact resolve eq19199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19199
  have eq19483 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq19554 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19483 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq19483
    | exact resolve eq19483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19483
  have eq19618 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq19554
  have eq26845 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ (τ X0)) (M.op (k X0 (σ X1)) X2)) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq724 (τ X0) X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq724
    | (have j0 := eq724 (τ X0) X1 X2
       grind)
    | exact resolve eq724 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq724
  have eq26990 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26845 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26845
    | (have j0 := eq26845 X0 X1 X2
       grind)
    | exact resolve eq26845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26845
  have eq27086 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26990 X0 X1 X2
       have i₂ := eq18306 (τ X0)
       grind)
    | exact superpose eq18306 eq26990
    | (have j0 := eq26990 X0 X1 X2
       grind)
    | exact resolve eq26990 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26990
  have eq27150 : ∀ X0 X1 X2 : G, (σ X1) = (σ (τ (M.op X0 X0))) ∨ (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27086 X0 X1 X2
       have i₂ := eq18299 X0
       grind)
    | exact superpose eq18299 eq27086
    | (have j0 := eq27086 X0 X1 X2
       grind)
    | exact resolve eq27086 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18299 eq27086
  have eq27203 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ X1) ∨ (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27150 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq27150
    | (have j0 := eq27150 X0 X1 X2
       grind)
    | exact resolve eq27150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27150
  have eq27248 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27203 X0 X1 X2
       have i₂ := eq18306 X1
       grind)
    | exact superpose eq18306 eq27203
    | (have j0 := eq27203 X0 X1 X2
       grind)
    | exact resolve eq27203 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27203
  have eq27291 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27248 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27248
    | (have j0 := eq27248 X0 X1 X2
       grind)
    | exact resolve eq27248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27248
  have eq100991 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27291 X1 X0 (M.op (σ X0) x)
       have i₂ := eq19248 X1 X0 x
       grind)
    | exact superpose eq19248 eq27291
    | (have j0 := eq27291 X1 X0 x
       have j1 := eq19248 X1 X0 x
       grind)
    | exact resolve eq27291 eq19248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19248 eq27291
  have eq101107 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq100991 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100991
  have eq101561 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq101107 X1 (σ X0)
       grind)
    | exact superpose eq101107 eq15
    | (have j1 := eq101107 X1 (σ X0)
       grind)
    | exact resolve eq15 eq101107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101107
  have eq101649 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101561 X0 X1
       have i₂ := eq18306 X0
       grind)
    | exact superpose eq18306 eq101561
    | (have j0 := eq101561 X0 X1
       grind)
    | exact resolve eq101561 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18306 eq101561
  have eq134952 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101649 x y
       grind)
    | exact superpose eq101649 eq16
    | (have j1 := eq101649 x y
       grind)
    | exact resolve eq16 eq101649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101649
  have eq138976 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq134952
       have i₂ := eq3200 y x
       grind)
    | exact superpose eq3200 eq134952
    | (have j1 := eq3200 y x
       grind)
    | (have r₁ := eq134952
       have r₂ := eq3200 y x
       grind)
    | exact resolve eq134952 eq3200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3200 eq134952
  have eq138977 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq138976
  have eq155634 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq138977
       grind)
    | exact superpose eq138977 eq10
    | exact resolve eq10 eq138977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138977
  have eq155992 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq155634
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq155634
    | exact resolve eq155634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155634
  have eq155993 : (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq155992
  have eq156155 : (M.op y y) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq155993
       grind)
    | exact superpose eq155993 eq10
    | exact resolve eq10 eq155993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155993
  have eq156513 : x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq156155
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq156155
    | exact resolve eq156155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156155
  have eq156514 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq156513
  have eq156687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18201 x
       have i₂ := eq156514
       grind)
    | exact superpose eq156514 eq18201
    | exact resolve eq18201 eq156514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18201 eq156514
  have eq156873 : x = (M.op y y) := by
    first
    | (have r₁ := eq156687
       have r₂ := eq16
       grind)
    | exact resolve eq156687 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156687
  have eq157014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19618 y
       have i₂ := eq156873
       grind)
    | exact superpose eq156873 eq19618
    | exact resolve eq19618 eq156873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19618 eq156873
  have eq157170 : False := by grind
  exact eq157170

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq64 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq74 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq344 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq723 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (σ X0) (σ X1) X2
       have i₂ := eq347 X0 X1
       grind)
    | exact superpose eq347 eq63
    | (have j1 := eq347 X0 X1
       grind)
    | exact resolve eq63 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (M.op (σ (k X0 X1)) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (σ X0) (σ X1) x
       have i₂ := eq347 X0 X1
       grind)
    | exact superpose eq347 eq64
    | (have j1 := eq347 X0 X1
       grind)
    | exact resolve eq64 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq731 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq74 (σ x)
       have i₂ := eq347 x x
       grind)
    | exact superpose eq347 eq74
    | (have j1 := eq347 X0 X0
       grind)
    | exact resolve eq74 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq347
  have eq737 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq738 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq742 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq737 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq737
    | (have j0 := eq737 X0
       grind)
    | exact resolve eq737 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq743 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq738 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq738
    | (have j0 := eq738 X0
       grind)
    | exact resolve eq738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq2690 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq742 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq742
    | exact resolve eq742 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2730 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2690 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2690
    | (have j0 := eq2690 X0
       grind)
    | exact resolve eq2690 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2690
  have eq2733 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2730 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2730
    | (have j0 := eq2730 X0
       grind)
    | exact resolve eq2730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq2734 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2733 X0
       have i₂ := eq20 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq20 eq2733
    | (have j0 := eq2733 X0
       grind)
    | exact resolve eq2733 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733
  have eq2735 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2734 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2734
    | (have j0 := eq2734 X0
       grind)
    | exact resolve eq2734 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq2736 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2735 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2735
    | (have j0 := eq2735 X0
       grind)
    | exact resolve eq2735 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq2752 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq2736
  have eq3086 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    grind
  clear eq743
  have eq3088 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3086 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3086
    | (have j0 := eq3086 X0
       grind)
    | exact resolve eq3086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq3147 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq344
    | exact resolve eq344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq3200 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3147 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3147
    | (have j0 := eq3147 X0 X1
       grind)
    | exact resolve eq3147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3147
  have eq3577 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (τ (k X2 (σ (M.op X0 X1)))) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (k X0 X1)
       have i₂ := eq3200 X1 X0
       grind)
    | exact superpose eq3200 eq24
    | (have j1 := eq3200 X1 X0
       grind)
    | exact resolve eq24 eq3200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3582 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (k X0 X1) X2
       have i₂ := eq3200 X1 X0
       grind)
    | exact superpose eq3200 eq30
    | (have j1 := eq3200 X1 X0
       grind)
    | exact resolve eq30 eq3200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3601 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3582 X0 X1 X2
       have i₂ := eq30 (M.op X0 X1) X2
       grind)
    | exact superpose eq30 eq3582
    | (have j0 := eq3582 X0 X1 X2
       grind)
    | exact resolve eq3582 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3582
  have eq3606 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (k (τ X2) (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3577 X0 X1 X2
       have i₂ := eq24 X2 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq3577
    | (have j0 := eq3577 X0 X1 X2
       grind)
    | exact resolve eq3577 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3577
  have eq6896 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X1) = X2 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3601 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3601
    | (have j0 := eq3601 X1 X2 X2
       grind)
    | exact resolve eq3601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3601
  have eq7025 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2752 X0
       have i₂ := eq6896 X0 X0 X0
       grind)
    | exact superpose eq6896 eq2752
    | (have j0 := eq2752 X0
       have j1 := eq6896 X0 X0 X0
       grind)
    | exact resolve eq2752 eq6896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752 eq6896
  have eq7097 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7025 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7025
  have eq7126 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq7097
  have eq7129 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X1) = X2 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3606 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3606
    | (have j0 := eq3606 X1 X2 X2
       grind)
    | exact resolve eq3606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3606
  have eq11580 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq74 (σ X0)
       have i₂ := eq3088 X0
       grind)
    | exact superpose eq3088 eq74
    | (have j1 := eq3088 X0
       grind)
    | exact resolve eq74 eq3088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3088
  have eq11622 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11580 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq11580
    | (have j0 := eq11580 X0
       grind)
    | exact resolve eq11580 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11580
  have eq11623 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq11622 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11622
  have eq11689 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) = (σ (k (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11623 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq11623
    | exact resolve eq11623 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11714 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ X0) (σ (k X0 X0))
       have i₂ := eq11623 X0
       grind)
    | exact superpose eq11623 eq63
    | exact resolve eq63 eq11623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11715 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ (k X0 (k X0 X0))) (M.op (σ (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) (σ (k X0 X0)) X1
       have i₂ := eq11623 X0
       grind)
    | exact superpose eq11623 eq63
    | exact resolve eq63 eq11623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11623
  have eq11757 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) = (k (σ (τ X0)) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11689 X0
       have i₂ := eq20 (k X0 X0) (τ X0)
       grind)
    | exact superpose eq20 eq11689
    | exact resolve eq11689 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11689
  have eq11790 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (σ (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11757 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11757
    | exact resolve eq11757 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11757
  have eq11814 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11790 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq11790
    | exact resolve eq11790 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11790
  have eq11880 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7129 X0 X0 X0
       have i₂ := eq11814 X0
       grind)
    | exact superpose eq11814 eq7129
    | (have j0 := eq7129 X0 X0 X0
       grind)
    | exact resolve eq7129 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7129
  have eq11927 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11880 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11880
  have eq11975 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11927 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq11927
    | (have j0 := eq11927 X0
       grind)
    | exact resolve eq11927 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11927
  have eq12196 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq11714 X0 X1
       have i₂ := eq11814 X0
       grind)
    | exact superpose eq11814 eq11714
    | exact resolve eq11714 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11714
  have eq12607 : ∀ X0 X2 : G, (σ (M.op X0 (k X0 X0))) = (M.op (σ X0) (M.op (σ (M.op X0 (k X0 X0))) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq63 (M.op x (σ X0)) (σ (M.op X0 (k X0 X0))) X2
       have i₂ := eq12196 X0 x
       grind)
    | exact superpose eq12196 eq63
    | exact resolve eq63 eq12196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12196
  have eq12836 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (k X0 X0) X1
       have i₂ := eq11975 X0
       grind)
    | exact superpose eq11975 eq63
    | (have j1 := eq11975 X0
       grind)
    | exact resolve eq63 eq11975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11975
  have eq14013 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ (M.op X0 (k X0 X0))) (M.op (σ (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11715 X0 X1
       have i₂ := eq11814 X0
       grind)
    | exact superpose eq11814 eq11715
    | exact resolve eq11715 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11715 eq11814
  have eq15349 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12607 X0 (M.op (σ (k X0 X0)) x)
       have i₂ := eq14013 X0 x
       grind)
    | exact superpose eq14013 eq12607
    | exact resolve eq12607 eq14013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12607 eq14013
  have eq17971 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12836 X0 X0
       have i₂ := eq7126 X0
       grind)
    | exact superpose eq7126 eq12836
    | (have j0 := eq12836 X0 x
       have j1 := eq7126 X0
       grind)
    | exact resolve eq12836 eq7126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7126 eq12836
  have eq18012 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq17971 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17971
  have eq18015 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq18012 X0
       have i₂ := eq63 X0 (M.op X0 X0) X0
       grind)
    | (have i₁ := eq18012 X0
       have i₂ := eq63 X0 (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) X0)) x
       grind)
    | exact superpose eq63 eq18012
    | (have j0 := eq18012 X0
       grind)
    | exact resolve eq18012 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq18012
  have eq18016 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18015 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18015
  have eq18029 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq18016 X0
       grind)
    | exact superpose eq18016 eq74
    | (have j1 := eq18016 X0
       grind)
    | exact resolve eq74 eq18016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq18016
  have eq18091 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18029 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18029
  have eq18201 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq15349 X0
       have i₂ := eq18091 X0
       grind)
    | exact superpose eq18091 eq15349
    | exact resolve eq15349 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15349
  have eq18238 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq18091 (σ X0)
       grind)
    | exact superpose eq18091 eq15
    | exact resolve eq15 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18245 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq18091 (τ X0)
       grind)
    | exact superpose eq18091 eq33
    | exact resolve eq33 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq18299 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18245 X0
       have i₂ := eq18091 X0
       grind)
    | exact superpose eq18091 eq18245
    | exact resolve eq18245 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18245
  have eq18306 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18238 X0
       have i₂ := eq18091 X0
       grind)
    | exact superpose eq18091 eq18238
    | exact resolve eq18238 eq18091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18091 eq18238
  have eq18797 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq723 (τ X0) X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq723
    | (have j0 := eq723 (τ X0) X1 X2
       grind)
    | exact resolve eq723 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq18980 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18797 X0 X1 X2
       have i₂ := eq18306 (τ X0)
       grind)
    | exact superpose eq18306 eq18797
    | (have j0 := eq18797 X0 X1 X2
       grind)
    | exact resolve eq18797 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18797
  have eq19065 : ∀ X0 X1 X2 : G, (σ X1) = (σ (τ (M.op X0 X0))) ∨ (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18980 X0 X1 X2
       have i₂ := eq18299 X0
       grind)
    | exact superpose eq18299 eq18980
    | (have j0 := eq18980 X0 X1 X2
       grind)
    | exact resolve eq18980 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18980
  have eq19137 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ X1) ∨ (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19065 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq19065
    | (have j0 := eq19065 X0 X1 X2
       grind)
    | exact resolve eq19065 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19065
  have eq19199 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19137 X0 X1 X2
       have i₂ := eq18306 X1
       grind)
    | exact superpose eq18306 eq19137
    | (have j0 := eq19137 X0 X1 X2
       grind)
    | exact resolve eq19137 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19137
  have eq19248 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (k X0 (σ X1)) (M.op (σ X1) X2)) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19199 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19199
    | (have j0 := eq19199 X0 X1 X2
       grind)
    | exact resolve eq19199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19199
  have eq19483 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq19554 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19483 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq19483
    | exact resolve eq19483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19483
  have eq19618 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq19554
  have eq26845 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ (τ X0)) (M.op (k X0 (σ X1)) X2)) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq724 (τ X0) X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq724
    | (have j0 := eq724 (τ X0) X1 X2
       grind)
    | exact resolve eq724 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq724
  have eq26990 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26845 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26845
    | (have j0 := eq26845 X0 X1 X2
       grind)
    | exact resolve eq26845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26845
  have eq27086 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26990 X0 X1 X2
       have i₂ := eq18306 (τ X0)
       grind)
    | exact superpose eq18306 eq26990
    | (have j0 := eq26990 X0 X1 X2
       grind)
    | exact resolve eq26990 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26990
  have eq27150 : ∀ X0 X1 X2 : G, (σ X1) = (σ (τ (M.op X0 X0))) ∨ (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27086 X0 X1 X2
       have i₂ := eq18299 X0
       grind)
    | exact superpose eq18299 eq27086
    | (have j0 := eq27086 X0 X1 X2
       grind)
    | exact resolve eq27086 eq18299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18299 eq27086
  have eq27203 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ X1) ∨ (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27150 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq27150
    | (have j0 := eq27150 X0 X1 X2
       grind)
    | exact resolve eq27150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27150
  have eq27248 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27203 X0 X1 X2
       have i₂ := eq18306 X1
       grind)
    | exact superpose eq18306 eq27203
    | (have j0 := eq27203 X0 X1 X2
       grind)
    | exact resolve eq27203 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27203
  have eq27291 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (M.op (k X0 (σ X1)) X2)) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27248 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27248
    | (have j0 := eq27248 X0 X1 X2
       grind)
    | exact resolve eq27248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27248
  have eq100740 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27291 X1 X0 (M.op (σ X0) x)
       have i₂ := eq19248 X1 X0 x
       grind)
    | exact superpose eq19248 eq27291
    | (have j0 := eq27291 X1 X0 x
       have j1 := eq19248 X1 X0 x
       grind)
    | exact resolve eq27291 eq19248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19248 eq27291
  have eq100856 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq100740 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100740
  have eq101303 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100856 X1 (σ X0)
       grind)
    | exact superpose eq100856 eq15
    | (have j1 := eq100856 X1 (σ X0)
       grind)
    | exact resolve eq15 eq100856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100856
  have eq101391 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101303 X0 X1
       have i₂ := eq18306 X0
       grind)
    | exact superpose eq18306 eq101303
    | (have j0 := eq101303 X0 X1
       grind)
    | exact resolve eq101303 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18306 eq101303
  have eq134593 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101391 x y
       grind)
    | exact superpose eq101391 eq16
    | (have j1 := eq101391 x y
       grind)
    | exact resolve eq16 eq101391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101391
  have eq138599 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq134593
       have i₂ := eq3200 y x
       grind)
    | exact superpose eq3200 eq134593
    | (have j1 := eq3200 y x
       grind)
    | (have r₁ := eq134593
       have r₂ := eq3200 y x
       grind)
    | exact resolve eq134593 eq3200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3200 eq134593
  have eq138600 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq138599
  have eq155201 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq138600
       grind)
    | exact superpose eq138600 eq10
    | exact resolve eq10 eq138600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138600
  have eq155561 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq155201
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq155201
    | exact resolve eq155201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155201
  have eq155562 : (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq155561
  have eq155725 : (M.op y y) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq155562
       grind)
    | exact superpose eq155562 eq10
    | exact resolve eq10 eq155562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155562
  have eq156085 : x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq155725
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq155725
    | exact resolve eq155725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155725
  have eq156086 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq156085
  have eq156260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18201 x
       have i₂ := eq156086
       grind)
    | exact superpose eq156086 eq18201
    | exact resolve eq18201 eq156086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18201 eq156086
  have eq156446 : x = (M.op y y) := by
    first
    | (have r₁ := eq156260
       have r₂ := eq16
       grind)
    | exact resolve eq156260 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156260
  have eq156587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19618 y
       have i₂ := eq156446
       grind)
    | exact superpose eq156446 eq19618
    | exact resolve eq19618 eq156446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19618 eq156446
  have eq156743 : False := by grind
  exact eq156743

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq19
  have eq36 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq189 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 (σ X1) (σ X0)
       have i₂ := eq58 X1 X0
       grind)
    | exact superpose eq58 eq21
    | (have j1 := eq58 X1 X0
       grind)
    | exact resolve eq21 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X1) (σ X0) X2
       have i₂ := eq58 X1 X0
       grind)
    | exact superpose eq58 eq21
    | (have j1 := eq58 X1 X0
       grind)
    | exact resolve eq21 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq58
  have eq207 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq202 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq210 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq207 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq207
    | (have j0 := eq207 X0
       grind)
    | exact resolve eq207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq390 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ (k (k X0 X0) X0)) (M.op (σ (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) (σ (k X0 X0)) X1
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq21
    | (have j1 := eq210 X0
       grind)
    | exact resolve eq21 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq720 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq189
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq189
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq189 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq721 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq720
  have eq809 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op X2 (σ (τ X1))) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq192 (τ X0) (τ X1) X2
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq192
    | (have j0 := eq192 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq192 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq829 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op X2 (σ (τ X1))) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq809 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq809
    | (have j0 := eq809 X0 X1 X2
       grind)
    | exact resolve eq809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq833 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq829 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq829
    | (have j0 := eq829 X0 X1 X2
       grind)
    | exact resolve eq829 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq835 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq833 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq833
    | (have j0 := eq833 X0 X1 X2
       grind)
    | exact resolve eq833 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq836 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq835 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq835
    | (have j0 := eq835 X0 X1 X2
       grind)
    | exact resolve eq835 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq837 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X2 X1) (k X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq836 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq836
    | (have j0 := eq836 X0 X1 X2
       grind)
    | exact resolve eq836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq838 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq837 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq837
    | (have j0 := eq837 X0 X1 X2
       grind)
    | exact resolve eq837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq923 : ∀ X0 X2 X3 : G, (k X2 X0) = (M.op X0 (M.op (k X2 X0) X3)) ∨ (M.op X2 X2) = X0 ∨ (M.op X0 X0) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq21 (M.op x X0) (k X2 X0) X3
       have i₂ := eq838 X2 X0 x
       grind)
    | exact superpose eq838 eq21
    | (have j1 := eq838 X2 X0 X2
       grind)
    | exact resolve eq21 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq937 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193 (τ X0) (τ X1) X2
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq193
    | (have j0 := eq193 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq193 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq193
  have eq970 : ∀ X0 X1 X2 : G, (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq937 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq937
    | (have j0 := eq937 X0 X1 X2
       grind)
    | exact resolve eq937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq973 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq970 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq970
    | (have j0 := eq970 X0 X1 X2
       grind)
    | exact resolve eq970 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq975 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq973 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq973
    | (have j0 := eq973 X0 X1 X2
       grind)
    | exact resolve eq973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq976 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq975 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq975
    | (have j0 := eq975 X0 X1 X2
       grind)
    | exact resolve eq975 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq977 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op (k X0 X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq976 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq976
    | (have j0 := eq976 X0 X1 X2
       grind)
    | exact resolve eq976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq978 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq977 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq977
    | (have j0 := eq977 X0 X1 X2
       grind)
    | exact resolve eq977 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq7921 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) = (M.op (σ (k (k (τ X0) (τ X0)) (τ X0))) (M.op (σ (k (τ X0) (τ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq390 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq390
    | (have j0 := eq390 (τ X0) X1
       grind)
    | exact resolve eq390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq7992 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = (M.op (σ (k (k (τ X0) (τ X0)) (τ X0))) (M.op (k (σ (τ X0)) X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7921 X0 X1
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq7921
    | (have j0 := eq7921 X0 X1
       grind)
    | exact resolve eq7921 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7921
  have eq7995 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ (k (k (τ X0) (τ X0)) (τ X0))) (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7992 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7992
    | (have j0 := eq7992 X0 X1
       grind)
    | exact resolve eq7992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7992
  have eq7996 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k (σ (k (τ X0) (τ X0))) X0) (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7995 X0 X1
       have i₂ := eq20 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq20 eq7995
    | (have j0 := eq7995 X0 X1
       grind)
    | exact resolve eq7995 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7995
  have eq7997 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k (k (σ (τ X0)) X0) X0) (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7996 X0 X1
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq7996
    | (have j0 := eq7996 X0 X1
       grind)
    | exact resolve eq7996 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7996
  have eq7998 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k (k X0 X0) X0) (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7997 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7997
    | (have j0 := eq7997 X0 X1
       grind)
    | exact resolve eq7997 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7997
  have eq8008 : ∀ X0 : G, (k X0 X0) = (M.op (k (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7998 X0 (M.op X0 x)
       have i₂ := eq978 X0 X0 x
       grind)
    | exact superpose eq978 eq7998
    | (have j0 := eq7998 X0 x
       have j1 := eq978 X0 X0 x
       grind)
    | exact resolve eq7998 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978 eq7998
  have eq8040 : ∀ X0 : G, (k X0 X0) = (M.op (k (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8008 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8008
  have eq8068 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (k (k X0 X0) X0) X0 X1
       have i₂ := eq8040 X0
       grind)
    | exact superpose eq8040 eq21
    | (have j1 := eq8040 X0
       grind)
    | exact resolve eq21 eq8040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8040
  have eq8226 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq923 X0 X0 (M.op X0 x)
       have i₂ := eq8068 X0 x
       grind)
    | exact superpose eq8068 eq923
    | (have j0 := eq923 X0 X0 x
       have j1 := eq8068 X0 x
       grind)
    | exact resolve eq923 eq8068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq8068
  have eq8246 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8226 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8226
  have eq8265 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq8246 X0
       grind)
    | exact superpose eq8246 eq36
    | (have j1 := eq8246 X0
       grind)
    | exact resolve eq36 eq8246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8246
  have eq8311 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8265
  have eq8447 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq8311 (σ X0)
       grind)
    | exact superpose eq8311 eq15
    | exact resolve eq15 eq8311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8527 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8447 X0
       have i₂ := eq8311 X0
       grind)
    | exact superpose eq8311 eq8447
    | exact resolve eq8447 eq8311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8311 eq8447
  have eq9090 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq9092 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq36 (σ X0)
       have i₂ := eq8527 X0
       grind)
    | exact superpose eq8527 eq36
    | exact resolve eq36 eq8527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9134 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9092 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq9092
    | exact resolve eq9092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9092
  have eq9136 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9090 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq9090
    | exact resolve eq9090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9090
  have eq9182 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9134 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq9134
    | exact resolve eq9134 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq9134
  have eq9184 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq9136
  have eq15034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9184 x
       have i₂ := eq721
       grind)
    | exact superpose eq721 eq9184
    | exact resolve eq9184 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq9184
  have eq15098 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq15034
       have r₂ := eq16
       grind)
    | exact resolve eq15034 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15034
  have eq15144 : (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15098
       have i₂ := eq8527 x
       grind)
    | exact superpose eq8527 eq15098
    | exact resolve eq15098 eq8527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15098
  have eq15164 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq15144
       have i₂ := eq8527 y
       grind)
    | exact superpose eq8527 eq15144
    | exact resolve eq15144 eq8527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15144
  have eq50870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9182 y
       have i₂ := eq15164
       grind)
    | exact superpose eq15164 eq9182
    | exact resolve eq9182 eq15164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15164
  have eq50958 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq50870
       have r₂ := eq16
       grind)
    | exact resolve eq50870 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50870
  have eq51930 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq8527 (M.op x x)
       have i₂ := eq50958
       grind)
    | exact superpose eq50958 eq8527
    | exact resolve eq8527 eq50958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50958
  have eq51981 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq51930
       have i₂ := eq21 x x x
       grind)
    | (have i₁ := eq51930
       have i₂ := eq21 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq21 eq51930
    | exact resolve eq51930 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq51930
  have eq52039 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq51981
       have i₂ := eq8527 y
       grind)
    | exact superpose eq8527 eq51981
    | exact resolve eq51981 eq8527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8527 eq51981
  have eq52040 : (σ x) = (σ (M.op y y)) := by grind
  clear eq52039
  have eq52093 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq52040
       grind)
    | exact superpose eq52040 eq10
    | exact resolve eq10 eq52040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52040
  have eq52254 : x = (M.op y y) := by
    first
    | (have i₁ := eq52093
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52093
    | exact resolve eq52093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52093
  have eq53066 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9182 y
       have i₂ := eq52254
       grind)
    | exact superpose eq52254 eq9182
    | exact resolve eq9182 eq52254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9182 eq52254
  have eq53154 : False := by grind
  exact eq53154

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq167 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq82
    | exact resolve eq82 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X0) (σ X1) X2
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq20
    | (have j1 := eq82 X0 X1
       grind)
    | exact resolve eq20 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (M.op (σ (k X0 X1)) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X0) (σ X1) x
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq21
    | (have j1 := eq82 X0 X1
       grind)
    | exact resolve eq21 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq82
  have eq1399 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X1)) X2)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
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
  have eq1447 : ∀ X0 X1 X2 : G, (M.op (σ (τ (k X0 X1))) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1399 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1399
    | (have j0 := eq1399 X0 X1 X2
       grind)
    | exact resolve eq1399 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1454 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1447 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1447
    | (have j0 := eq1447 X0 X1 X2
       grind)
    | exact resolve eq1447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq1460 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1454 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1454
    | (have j0 := eq1454 X0 X1 X2
       grind)
    | exact resolve eq1454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1465 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1460 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1460
    | (have j0 := eq1460 X0 X1 X2
       grind)
    | exact resolve eq1460 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1470 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1465 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1465
    | (have j0 := eq1465 X0 X1 X2
       grind)
    | exact resolve eq1465 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1473 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1470 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1470
    | (have j0 := eq1470 X0 X1 X2
       grind)
    | exact resolve eq1470 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1686 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ (k X0 X0)) = (M.op (σ X0) (M.op (σ (k X0 X0)) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1687 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (M.op (σ (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1686 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq1994 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq167 X0 X1 X2
       grind)
    | exact superpose eq167 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq167 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq167 X0 X1 X2
       grind)
    | exact resolve eq13 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2008 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1994 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq2009 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2008 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2010 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2009 X0 X1 X2
       have i₂ := eq32 X0 X1 X2
       grind)
    | exact superpose eq32 eq2009
    | (have j0 := eq2009 X0 X1 X2
       grind)
    | exact resolve eq2009 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2009
  have eq3675 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) = (M.op X0 (M.op (σ (k (τ X0) (τ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1687 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1687
    | exact resolve eq1687 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq3725 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = (M.op X0 (M.op (k (σ (τ X0)) X0) X1)) ∨ (M.op X0 X0) = X0 := by
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
  have eq3726 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3725 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3725
    | (have j0 := eq3725 X0 X1
       grind)
    | exact resolve eq3725 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq3731 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3726 X0 (M.op X0 x)
       have i₂ := eq1473 X0 X0 x
       grind)
    | exact superpose eq1473 eq3726
    | (have j0 := eq3726 X0 x
       have j1 := eq1473 X0 X0 x
       grind)
    | exact resolve eq3726 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473 eq3726
  have eq3758 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3731
  have eq3777 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq3758
  have eq3809 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3777 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq3932 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
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
  have eq3941 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
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
  have eq3988 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3941 X0
       have i₂ := eq3809 X0
       grind)
    | exact superpose eq3809 eq3941
    | exact resolve eq3941 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3941
  have eq3996 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3932 X0
       have i₂ := eq3809 X0
       grind)
    | exact superpose eq3809 eq3932
    | exact resolve eq3932 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3932
  have eq4369 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4392 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4369 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq4369
    | exact resolve eq4369 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4369
  have eq4415 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq4392
  have eq84978 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2010 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq84979 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq84978 X0 X1 X2
       have j1 := eq167 X0 X1 X2
       grind)
    | (have r₁ := eq84978 X0 X1 X2
       have r₂ := eq167 X0 X1 X2
       grind)
    | exact resolve eq84978 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq84978
  have eq85232 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84979 X0 X1 X2
       have i₂ := eq3996 X2
       grind)
    | exact superpose eq3996 eq84979
    | (have j0 := eq84979 X0 X1 X2
       grind)
    | exact resolve eq84979 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84979
  have eq508413 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (k X0 (σ (τ X1))) (σ X2)) ∨ (k X0 (σ (τ X1))) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85232 X0 (τ X1) X2
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq85232
    | (have j0 := eq85232 X0 (τ X1) X2
       grind)
    | exact resolve eq85232 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq85232
  have eq509263 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (k X0 X1) (σ X2)) ∨ (k X0 (σ (τ X1))) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq508413 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq508413
    | (have j0 := eq508413 X0 X1 X2
       grind)
    | exact resolve eq508413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508413
  have eq509447 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (k X0 X1) (σ X2)) ∨ (k X0 (σ (τ X1))) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509263 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq509263
    | (have j0 := eq509263 X0 X1 X2
       grind)
    | exact resolve eq509263 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509263
  have eq509576 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (k X0 X1) (σ X2)) ∨ (k X0 X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509447 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq509447
    | (have j0 := eq509447 X0 X1 X2
       grind)
    | exact resolve eq509447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509447
  have eq510142 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (M.op (k X1 X2) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509576 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq509576
    | (have j0 := eq509576 X1 X2 (τ X0)
       grind)
    | exact resolve eq509576 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509576
  have eq510543 : ∀ X0 X1 X2 : G, (k X1 X2) = (σ (τ (M.op X0 X0))) ∨ (k (k X1 X2) X0) = (M.op (k X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq510142 X0 X1 X2
       have i₂ := eq3988 X0
       grind)
    | exact superpose eq3988 eq510142
    | (have j0 := eq510142 X0 X1 X2
       grind)
    | exact resolve eq510142 eq3988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3988 eq510142
  have eq510660 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (M.op (k X1 X2) X0) ∨ (M.op X0 X0) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq510543 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq510543
    | (have j0 := eq510543 X0 X1 X2
       grind)
    | exact resolve eq510543 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510543
  have eq510889 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq510660 X0 X0 X0
       have i₂ := eq3809 X0
       grind)
    | exact superpose eq3809 eq510660
    | exact resolve eq510660 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809 eq510660
  have eq518142 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq510889 (M.op x x) X1
       have i₂ := eq20 x x x
       grind)
    | exact superpose eq20 eq510889
    | exact resolve eq510889 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq510889
  have eq519510 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq518142 (σ X0) (σ X1)
       grind)
    | exact superpose eq518142 eq15
    | (have j1 := eq518142 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq518142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519535 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq518142 (τ X0) X1
       grind)
    | exact superpose eq518142 eq18
    | (have j1 := eq518142 (τ X0) X1
       grind)
    | exact resolve eq18 eq518142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq518142
  have eq519841 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq519510 X0 X1
       have i₂ := eq3996 X1
       grind)
    | exact superpose eq3996 eq519510
    | (have j0 := eq519510 X0 X1
       grind)
    | exact resolve eq519510 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3996 eq519510
  have eq527132 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq519535 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq519535
    | exact resolve eq519535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519535
  have eq527965 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq527132 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq527132
    | (have j0 := eq527132 X0 X1
       grind)
    | exact resolve eq527132 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527132
  have eq544687 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq519841 x y
       grind)
    | exact superpose eq519841 eq16
    | (have j1 := eq519841 x y
       grind)
    | exact resolve eq16 eq519841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519841
  have eq549270 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq544687
       have i₂ := eq527965 x y
       grind)
    | exact superpose eq527965 eq544687
    | (have j1 := eq527965 x y
       grind)
    | (have r₁ := eq544687
       have r₂ := eq527965 x y
       grind)
    | exact resolve eq544687 eq527965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527965 eq544687
  have eq549273 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq549270
  have eq549350 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq549273
       grind)
    | exact superpose eq549273 eq10
    | exact resolve eq10 eq549273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549273
  have eq549948 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq549350
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq549350
    | exact resolve eq549350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549350
  have eq549949 : x = (M.op y y) := by grind
  clear eq549948
  have eq551958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4415 y
       have i₂ := eq549949
       grind)
    | exact superpose eq549949 eq4415
    | exact resolve eq4415 eq549949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4415 eq549949
  have eq552399 : False := by grind
  exact eq552399
