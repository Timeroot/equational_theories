import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq71 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op X2 X1) (M.op X0 X0)) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 (σ X0) (σ X1)
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq69
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq69 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq90 y y
       grind)
    | exact superpose eq90 eq70
    | (have j1 := eq90 y y
       grind)
    | exact resolve eq70 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq107 : (k y (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq89
       have i₂ := eq90 sF3 sF1
       grind)
    | exact superpose eq90 eq89
    | (have j1 := eq90 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq89 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq90
    | (have j0 := eq90 (σ y) (σ x)
       grind)
    | exact resolve eq90 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq119
    | exact resolve eq119 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq120
       have r₂ := eq27
       grind)
    | exact resolve eq120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq27
    | exact resolve eq27 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq125 eq51
    | exact resolve eq51 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq224 eq14
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op y (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq232 eq50
    | exact resolve eq50 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq317 : (σ x) = (M.op (σ y) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq272 eq224
    | exact resolve eq224 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq322 : (σ x) = (M.op (σ y) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by grind
  clear eq317
  have eq342 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq73
    | (have r₁ := eq73
       have r₂ := eq125
       grind)
    | exact resolve eq73 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq406 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq405
  have eq409 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq406 eq116
    | exact resolve eq116 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq412 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq409
  have eq423 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq412 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq412
       grind)
    | exact resolve eq13 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq437 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq423 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq441 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq497 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq497
    | exact resolve eq497 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq509 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq496 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq496
    | exact resolve eq496 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq521 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq475 X0 X1 X2 X3 X4
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq475
    | exact resolve eq475 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq605 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (σ X0) X1 X2 X3
       have i₂ := eq94 X0 X0
       grind)
    | exact superpose eq94 eq52
    | (have j1 := eq94 X0 X0
       grind)
    | exact resolve eq52 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq94
  have eq650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq437 eq116
    | exact resolve eq116 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq437
  have eq653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq650
  have eq658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq653
    | exact resolve eq653 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq660 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq658
       have r₂ := eq27
       grind)
    | exact resolve eq658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq663 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq660 eq29
    | exact resolve eq29 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq665 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq660 eq40
    | exact resolve eq40 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq678 : (σ x) = (M.op (σ (M.op x y)) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq660 eq322
    | exact resolve eq322 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq660
  have eq681 : (σ x) = (M.op (σ (M.op x y)) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by grind
  clear eq678
  have eq693 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq665
    | exact resolve eq665 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq665
  have eq695 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq663
    | exact resolve eq663 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq663
  have eq716 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (k (M.op (M.op X1 X0) (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1501 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (σ (k X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq1522 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1501 X0
       have i₂ := eq16 (k X0 y)
       grind)
    | exact superpose eq16 eq1501
    | exact resolve eq1501 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1956 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq441 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq441 X0 X0 X0
       grind)
    | exact superpose eq441 eq441
    | exact resolve eq441 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2000 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X1 (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq441 X0 X0 X0
       grind)
    | exact superpose eq441 eq13
    | (have j0 := eq13 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq13 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2001 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq441 X0 X0 X0
       grind)
    | exact superpose eq441 eq14
    | exact resolve eq14 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2002 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq441 X0 X0 X0
       grind)
    | exact superpose eq441 eq50
    | exact resolve eq50 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2008 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq224 (M.op X0 (M.op X0 X0))
       have i₂ := eq441 X0 X0 X0
       grind)
    | exact superpose eq441 eq224
    | exact resolve eq224 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq2018 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq491 (M.op x (M.op x x)) x
       have i₂ := eq441 x x x
       grind)
    | exact superpose eq441 eq491
    | exact resolve eq491 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4874 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq349 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1)))
       have i₂ := eq348 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq348 eq349
    | exact resolve eq349 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6088 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq509 X0 X1
       have i₂ := eq508 X0 X1
       grind)
    | exact superpose eq508 eq509
    | exact resolve eq509 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq6656 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op (M.op X3 X4) X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq474 X2 X1 X3 X4 (M.op X0 (M.op X0 X0))
       have i₂ := eq441 X0 X0 X0
       grind)
    | exact superpose eq441 eq474
    | exact resolve eq474 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8782 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq2008 X0
       grind)
    | exact superpose eq2008 eq342
    | exact resolve eq342 eq2008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8922 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8782 eq474
    | exact resolve eq474 eq8782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8782
  have eq8970 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8922 x x
       have i₂ := eq491 sF3 (M.op x x)
       grind)
    | exact superpose eq491 eq8922
    | exact resolve eq8922 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8922
  have eq8971 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8970
    | exact resolve eq8970 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8970
  have eq8980 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) = (k (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) ∨ (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq716 (M.op X1 (M.op X0 X1)) (M.op X0 X1)
       have i₂ := eq508 X0 X1
       grind)
    | exact superpose eq508 eq716
    | (have j0 := eq716 (M.op X1 (M.op X0 X1)) X1
       grind)
    | exact resolve eq716 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq9190 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (k (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) ∨ (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8980 X0 X0
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq8980
    | (have j0 := eq8980 X0 X1
       grind)
    | exact resolve eq8980 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8980
  have eq9268 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) = (k (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) ∨ (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9190 X0 X1
       have i₂ := eq508 X0 X1
       grind)
    | exact superpose eq508 eq9190
    | (have j0 := eq9190 X0 X1
       grind)
    | exact resolve eq9190 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9190
  have eq9331 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) ∨ (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9268 X0 X1
       have i₂ := eq53 sF3 (M.op sF4 (M.op X0 X1))
       grind)
    | exact superpose eq53 eq9268
    | (have j0 := eq9268 X0 X1
       grind)
    | exact resolve eq9268 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9268
  have eq9348 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) ∨ (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq6088 eq9331
    | (have j0 := eq9331 X0 X1
       grind)
    | exact resolve eq9331 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9331
  have eq9361 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9348 X0 X1
       have i₂ := eq53 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq9348
    | (have j0 := eq9348 X0 X1
       grind)
    | exact resolve eq9348 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9348
  have eq9364 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) ∨ (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9361 X0 X1
       have i₂ := eq508 X0 X1
       grind)
    | exact superpose eq508 eq9361
    | (have j0 := eq9361 X0 X1
       grind)
    | exact resolve eq9361 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9361
  have eq9365 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op y (M.op (M.op x y) (M.op X0 X1))) ∨ (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq6088 eq9364
    | (have j0 := eq9364 X0 X1
       grind)
    | exact resolve eq9364 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9364
  have eq9369 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8971 eq50
    | exact resolve eq50 eq8971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq8971
  have eq9539 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq521 X0 X1 X2 X3 X4
       have i₂ := eq508 X0 X1
       grind)
    | exact superpose eq508 eq521
    | exact resolve eq521 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq9540 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq6088 eq9539
    | exact resolve eq9539 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9539
  have eq10007 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op X0 X1) (M.op X0 X1)))) = (M.op (M.op X2 (M.op y (M.op (M.op x y) (M.op (M.op X0 X1) (M.op X0 X1))))) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 (M.op (M.op X2 x) (M.op (M.op X2 x) (M.op X2 x))) x
       have i₂ := eq9540 (M.op X2 x) (M.op X2 x) X2 x (M.op X2 x)
       grind)
    | exact superpose eq9540 eq491
    | exact resolve eq491 eq9540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9540
  have eq10049 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X1)))) = (M.op (M.op X2 (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X1))))) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10007 X0 X1 X2
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq10007
    | exact resolve eq10007 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq10007
  have eq10143 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X1)))) = (M.op (M.op X2 (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X1))))) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10049 X0 X1 X2
       have i₂ := eq508 X0 X1
       grind)
    | exact superpose eq508 eq10049
    | exact resolve eq10049 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10049
  have eq10194 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X1)))) = (M.op (M.op X2 (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X1))))) (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq6088 eq10143
    | exact resolve eq10143 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6088 eq10143
  have eq10230 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq349 eq10194
    | exact resolve eq10194 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10194
  have eq10301 : (σ y) = (M.op y (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq9369
    | exact resolve eq9369 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq9369
  have eq10325 : (σ y) = (M.op y (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq10301
  have eq12606 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k (τ X0) (τ X0)))) (M.op X0 (M.op X3 X3))) = X3 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq605 (τ X0) X1 X2 X3
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq605
    | exact resolve eq605 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq12725 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (k X0 (σ (τ X0)))) (M.op X0 (M.op X3 X3))) = X3 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12606 X0 X1 X2 X3
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq12606
    | (have j0 := eq12606 X0 X1 X2 X3
       grind)
    | exact resolve eq12606 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq12606
  have eq12748 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (k X0 X0)) (M.op X0 (M.op X3 X3))) = X3 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12725 X0 X1 X2 X3
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12725
    | (have j0 := eq12725 X0 X1 X2 X3
       grind)
    | exact resolve eq12725 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12725
  have eq13163 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10325 eq681
    | exact resolve eq681 eq10325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq10325
  have eq13199 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13163
  have eq22305 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq441 X1 X0 X0
       have i₂ := eq2002 X0
       grind)
    | exact superpose eq2002 eq441
    | exact resolve eq441 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq22381 : ∀ X0 X1 X2 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op y (M.op y y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2002 eq474
    | exact resolve eq474 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq22424 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq22381 x x x
       have i₂ := eq474 y y x x x
       grind)
    | exact superpose eq474 eq22381
    | exact resolve eq22381 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22381
  have eq48535 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq474 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq2001 X0 X0 X1
       grind)
    | exact superpose eq2001 eq474
    | exact resolve eq474 eq2001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq48603 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48535 X0 X1 x x x
       have i₂ := eq474 X0 X0 x x x
       grind)
    | exact superpose eq474 eq48535
    | exact resolve eq48535 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq48535
  have eq65956 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq342 X2
       have i₂ := eq1956 X2 X0 X1
       grind)
    | exact superpose eq1956 eq342
    | exact resolve eq342 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq1956
  have eq307639 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq348 X0 X0 (k X0 X0) (M.op x x)
       have i₂ := eq12748 X0 x x X0
       grind)
    | exact superpose eq12748 eq348
    | (have j1 := eq12748 X0 x x x
       grind)
    | exact resolve eq348 eq12748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq12748
  have eq330149 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op (σ x) X0) (M.op X0 (M.op X0 X0)))) (M.op (M.op (σ x) X0) (M.op X0 (M.op X0 X0)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2008 eq4874
    | exact resolve eq4874 eq2008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008 eq4874
  have eq330714 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq330149 X0 X1
       have i₂ := eq2018 X0 sF2
       grind)
    | exact superpose eq2018 eq330149
    | exact resolve eq330149 eq2018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330149
  have eq330933 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq349 eq330714
    | exact resolve eq330714 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330714
  have eq2503354 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op y (M.op (M.op x y) (M.op X0 X1))) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq10230 eq9365
    | (have j0 := eq9365 X0 X1
       grind)
    | exact resolve eq9365 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9365 eq10230
  have eq2507128 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) X0) (M.op y (M.op (M.op x y) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))))) ∨ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6656 X0 X0 (M.op X0 X0) X1 X2
       have i₂ := eq2503354 (M.op X0 X0) (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq2503354 eq6656
    | (have j1 := eq2503354 (M.op X0 X0) (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq6656 eq2503354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6656 eq2503354
  have eq2508486 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) X0) (M.op X0 (M.op X0 X0))) ∨ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq349 eq2507128
    | (have j0 := eq2507128 X0 X1 X2
       grind)
    | exact resolve eq2507128 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq2507128
  have eq2509826 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq2508486 X0 x x
       have i₂ := eq2018 X0 (M.op x x)
       grind)
    | exact superpose eq2018 eq2508486
    | (have j0 := eq2508486 X0 x x
       grind)
    | exact resolve eq2508486 eq2018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018 eq2508486
  have eq2510614 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 X0))))) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2509826 X0
       have i₂ := eq508 X0 (M.op X0 X0)
       grind)
    | exact superpose eq508 eq2509826
    | (have j0 := eq2509826 X0
       grind)
    | exact resolve eq2509826 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509826
  have eq2510896 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq350 eq2510614
    | (have j0 := eq2510614 X0
       grind)
    | exact resolve eq2510614 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq2510614
  have eq2511038 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = (k (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2510896 x
       have i₂ := eq508 x x
       grind)
    | exact superpose eq508 eq2510896
    | (have j0 := eq2510896 X0
       grind)
    | exact resolve eq2510896 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq2510896
  have eq2511117 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq2511038
    | (have j0 := eq2511038 X0
       grind)
    | exact resolve eq2511038 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2511038
  have eq4632713 : (τ (σ x)) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13199 eq107
    | exact resolve eq107 eq13199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13199
  have eq4633273 : (τ (σ x)) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4632713
       have r₂ := eq127
       grind)
    | exact resolve eq4632713 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq4632713
  have eq4633287 : x = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq4633273
    | exact resolve eq4633273 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4633273
  have eq4633311 : x = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4633287 eq1522
    | exact resolve eq1522 eq4633287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522 eq4633287
  have eq4633404 : x = (k y y) ∨ x = (M.op x y) := by grind
  clear eq4633311
  have eq6268930 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq307639 y
       have i₂ := eq4633404
       grind)
    | exact superpose eq4633404 eq307639
    | (have j0 := eq307639 y
       grind)
    | exact resolve eq307639 eq4633404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6270821 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6268930
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6268930
    | exact resolve eq6268930 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6268930
  have eq6279523 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 y) = (M.op y X0) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq6270821
       grind)
    | exact superpose eq6270821 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq6270821
       grind)
    | exact resolve eq13 eq6270821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6270821
  have eq6280866 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6279523 X0
       grind)
    | (have r₁ := eq6279523 X0
       have r₂ := eq695
       grind)
    | exact resolve eq6279523 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq6279523
  have eq6281062 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6280866 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq6280866 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq6280866 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6280866
  have eq6283019 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4633404
       have i₂ := eq6281062 y
       grind)
    | exact superpose eq6281062 eq4633404
    | exact resolve eq4633404 eq6281062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4633404 eq6281062
  have eq6283819 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq6283019
  have eq6286855 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq330933 y y
       have i₂ := eq6283819
       grind)
    | exact superpose eq6283819 eq330933
    | exact resolve eq330933 eq6283819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330933 eq6283819
  have eq6286983 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6286855
  have eq6287223 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6286983
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6286983
    | exact resolve eq6286983 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6286983
  have eq6287224 : x = (M.op x y) := by grind
  clear eq6287223
  have eq6287867 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq6287224 eq20
    | exact resolve eq20 eq6287224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6287917 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq6287224 eq216
    | exact resolve eq216 eq6287224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6288250 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq6287224 eq22424
    | exact resolve eq22424 eq6287224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22424
  have eq6288459 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6288250
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6288250
    | exact resolve eq6288250 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288250
  have eq6288663 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq6287867
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6287867
    | exact resolve eq6287867 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6287867
  have eq6288698 : x = (M.op y y) := by
    first
    | exact superpose eq6287224 eq6288459
    | exact resolve eq6288459 eq6287224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288459
  have eq6288794 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq6288663 eq26
    | exact resolve eq26 eq6288663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq6291436 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq103
       have i₂ := eq6288698
       grind)
    | exact superpose eq6288698 eq103
    | exact resolve eq103 eq6288698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq6292217 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq65956 X0 y y
       have i₂ := eq6288698
       grind)
    | exact superpose eq6288698 eq65956
    | exact resolve eq65956 eq6288698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65956 eq6288698
  have eq6292454 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq6292217 x
       have i₂ := eq48603 x x
       grind)
    | exact superpose eq48603 eq6292217
    | exact resolve eq6292217 eq48603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48603 eq6292217
  have eq6292891 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq6291436
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6291436
    | exact resolve eq6291436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6291436
  have eq6293208 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq6288663 eq6292891
    | exact resolve eq6292891 eq6288663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6292891
  have eq6293383 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6288794 eq107
    | exact resolve eq107 eq6288794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq6294416 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq6293383
       have r₂ := eq27
       grind)
    | exact resolve eq6293383 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6293383
  have eq6294622 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6287224 eq6294416
    | exact resolve eq6294416 eq6287224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6294416
  have eq6294717 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq69
       have i₂ := eq6294622
       grind)
    | exact superpose eq6294622 eq69
    | exact resolve eq69 eq6294622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6294931 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6294717
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq6294717
    | exact resolve eq6294717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6294717
  have eq6295011 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq6288663 eq6294931
    | exact resolve eq6294931 eq6288663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6294931
  have eq6302150 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq6293208 eq307639
    | (have j0 := eq307639 (σ y)
       grind)
    | exact resolve eq307639 eq6293208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307639
  have eq6302239 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq6288794 eq6302150
    | exact resolve eq6302150 eq6288794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288794 eq6302150
  have eq6309221 : (M.op y (M.op (M.op x y) (M.op x y))) = (k (M.op y (M.op (M.op x y) (M.op x y))) (M.op x y)) ∨ (M.op y (M.op (M.op x y) (M.op x y))) = (M.op (M.op y (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq22305 eq2511117
    | exact resolve eq2511117 eq22305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22305 eq2511117
  have eq6310509 : (M.op y (M.op x x)) = (k (M.op y (M.op x x)) x) ∨ (M.op y (M.op (M.op x y) (M.op x y))) = (M.op (M.op y (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq6287224 eq6309221
    | exact resolve eq6309221 eq6287224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6309221
  have eq6310960 : y = (k y x) ∨ (M.op y (M.op (M.op x y) (M.op x y))) = (M.op (M.op y (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq6310509
       have i₂ := eq6292454
       grind)
    | exact superpose eq6292454 eq6310509
    | exact resolve eq6310509 eq6292454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6310509
  have eq6311380 : y = (τ (M.op (σ x) (σ y))) ∨ (M.op y (M.op (M.op x y) (M.op x y))) = (M.op (M.op y (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq6310960
       have i₂ := eq6294622
       grind)
    | exact superpose eq6294622 eq6310960
    | exact resolve eq6310960 eq6294622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6294622 eq6310960
  have eq6311710 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6311380
       have i₂ := eq491 sF0 y
       grind)
    | exact superpose eq491 eq6311380
    | exact resolve eq6311380 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq6311380
  have eq6311888 : (M.op y (M.op x y)) = (M.op y (M.op y (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq216 eq6311710
    | exact resolve eq6311710 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq6311710
  have eq6312045 : (M.op y x) = (M.op y (M.op y x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6287224 eq6311888
    | exact resolve eq6311888 eq6287224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6311888
  have eq6312128 : (M.op x x) = (M.op y (M.op x x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6312045
       have i₂ := eq6287917
       grind)
    | exact superpose eq6287917 eq6312045
    | exact resolve eq6312045 eq6287917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6287917 eq6312045
  have eq6312183 : y = (M.op x x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6312128
       have i₂ := eq6292454
       grind)
    | exact superpose eq6292454 eq6312128
    | exact resolve eq6312128 eq6292454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6292454 eq6312128
  have eq6312353 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2000 x x
       have i₂ := eq6312183
       grind)
    | exact superpose eq6312183 eq2000
    | exact resolve eq2000 eq6312183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000 eq6312183
  have eq6313577 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq6312353 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6312353
    | (have j0 := eq6312353 X0
       grind)
    | exact resolve eq6312353 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6312353
  have eq6314000 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq6313577 X0
       grind)
    | (have r₁ := eq6313577 X0
       have r₂ := eq6287224
       grind)
    | exact resolve eq6313577 eq6287224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6313577
  have eq6314284 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq6314000 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6314000
    | (have j0 := eq6314000 X0
       grind)
    | exact resolve eq6314000 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6314000
  have eq6314449 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq6287224 eq6314284
    | exact resolve eq6314284 eq6287224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6287224 eq6314284
  have eq6556082 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq69
       have i₂ := eq6314449 y
       grind)
    | exact superpose eq6314449 eq69
    | exact resolve eq69 eq6314449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq6314449
  have eq6557324 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6288663 eq6556082
    | exact resolve eq6556082 eq6288663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6556082
  have eq6557914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6295011 eq6557324
    | exact resolve eq6557324 eq6295011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6295011 eq6557324
  have eq6558311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6557914
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6557914
    | exact resolve eq6557914 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6557914
  have eq6558570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq6558311
    | exact resolve eq6558311 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6558311
  have eq6558723 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq6558570
       have r₂ := eq27
       grind)
    | exact resolve eq6558570 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6558570
  have eq6560475 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6558723 eq15
    | exact resolve eq15 eq6558723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6558723
  have eq6561316 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6560475
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6560475
    | exact resolve eq6560475 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6560475
  have eq6561490 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq6561316 eq27
    | exact resolve eq27 eq6561316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq8060967 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq6561316 eq6302239
    | exact resolve eq6302239 eq6561316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6302239 eq6561316
  have eq8060968 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq8060967
  have eq8061358 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq8060968 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq8060968
       grind)
    | exact resolve eq13 eq8060968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8062257 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq8061358 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8061358
  have eq8066401 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq8062257 eq6293208
    | exact resolve eq6293208 eq8062257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6293208 eq8062257
  have eq8067043 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq8066401
  have eq8068311 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq8067043 eq8060968
    | exact resolve eq8060968 eq8067043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8060968 eq8067043
  have eq8069414 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq8068311
  have eq8070102 : x = y := by
    first
    | (have r₁ := eq8069414
       have r₂ := eq6561490
       grind)
    | exact resolve eq8069414 eq6561490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8069414
  have eq8071464 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8070102
       grind)
    | exact superpose eq8070102 eq24
    | exact resolve eq24 eq8070102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8070102
  have eq8073847 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8071464
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8071464
    | exact resolve eq8071464 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8071464
  have eq8074162 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6288663 eq8073847
    | exact resolve eq8073847 eq6288663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288663 eq8073847
  have eq8074338 : False := by grind
  exact eq8074338

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq100 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq110 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq103 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq103
    | exact resolve eq103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq103 X0 X0
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq103 X1 X0
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq112
    | exact resolve eq112 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq118 X0
       have i₂ := eq103 X0 X0
       grind)
    | exact superpose eq103 eq118
    | exact resolve eq118 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 (M.op X1 X0)
       have i₂ := eq103 X1 X0
       grind)
    | exact superpose eq103 eq114
    | exact resolve eq114 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq114 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq114
    | exact resolve eq114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq9
    | exact resolve eq9 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq122 X0
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq122
    | exact resolve eq122 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq230 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X1 (M.op (σ (M.op x x)) (M.op X0 X0)) (σ x)
       have i₂ := eq100 x X0
       grind)
    | exact superpose eq100 eq110
    | exact resolve eq110 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq110
  have eq287 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq125 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq125 X0 X0
       grind)
    | exact superpose eq125 eq125
    | exact resolve eq125 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq125 X1 X0
       grind)
    | exact superpose eq125 eq9
    | exact resolve eq9 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq125 X0 X0
       grind)
    | exact superpose eq125 eq9
    | exact resolve eq9 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq125 X1 X1
       grind)
    | exact superpose eq125 eq230
    | exact resolve eq230 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq230
  have eq408 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq300 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq300 X0 X0 X0
       grind)
    | exact superpose eq300 eq300
    | exact resolve eq300 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq301 (M.op X1 X0) X2 X3
       have i₂ := eq103 X1 X0
       grind)
    | exact superpose eq103 eq301
    | exact resolve eq301 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq301 X2 X3 X4
       have i₂ := eq301 X2 X0 X1
       grind)
    | exact superpose eq301 eq301
    | exact resolve eq301 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq301 (M.op X0 X1) X1 X0
       have i₂ := eq103 X0 X1
       grind)
    | exact superpose eq103 eq301
    | exact resolve eq301 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq309 X2 X3
       have i₂ := eq301 X2 X0 X1
       grind)
    | exact superpose eq301 eq309
    | exact resolve eq309 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq484 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114 X2
       have i₂ := eq301 X2 X0 X1
       grind)
    | exact superpose eq301 eq114
    | exact resolve eq114 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq474 X0 X1
       grind)
    | exact superpose eq474 eq121
    | exact resolve eq121 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq581 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq484 (M.op X2 (M.op X0 X0)) (M.op x (M.op X2 X2)) X1
       have i₂ := eq300 X2 x X0
       grind)
    | exact superpose eq300 eq484
    | exact resolve eq484 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = (M.op (M.op (M.op X1 (M.op X2 X0)) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq484 X0 X2 (M.op (M.op X1 (M.op X2 X0)) X0)
       have i₂ := eq484 (M.op X2 X0) X1 X0
       grind)
    | exact superpose eq484 eq484
    | exact resolve eq484 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq656 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq647
    | (have j0 := eq647 X0 X1
       grind)
    | exact resolve eq647 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq733 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X0 X0)) = (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X4)) (M.op X0 X0))) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq481 X4 X3 (M.op (M.op X2 (M.op X3 X4)) (M.op X0 X0)) X1
       have i₂ := eq9 X0 (M.op X3 X4) X2
       grind)
    | exact superpose eq9 eq481
    | exact resolve eq481 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301 (M.op X1 (M.op (M.op X2 X1) X0)) X0 x
       have i₂ := eq481 X1 X2 X0 x
       grind)
    | exact superpose eq481 eq301
    | exact resolve eq301 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) = (M.op (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq484 (M.op X3 X0) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0)
       have i₂ := eq481 (M.op X2 (M.op X3 X0)) X1 X0 X3
       grind)
    | exact superpose eq481 eq484
    | exact resolve eq484 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq745 X0 X1 X2
       have i₂ := eq103 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq103 eq745
    | exact resolve eq745 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq764 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq755 X0 X1 X2
       have i₂ := eq474 (M.op (M.op X2 X1) X0) X1
       grind)
    | exact superpose eq474 eq755
    | exact resolve eq755 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq755
  have eq765 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq764 X0 X1 X2
       have i₂ := eq481 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq481 eq764
    | exact resolve eq764 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq766 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq604 X0 X1 X2
       have i₂ := eq765 X0 (M.op X2 X0) X1
       grind)
    | exact superpose eq765 eq604
    | exact resolve eq604 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq767 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq746 X0 X1 X2 X3
       have i₂ := eq765 X0 (M.op X2 (M.op X3 X0)) X1
       grind)
    | exact superpose eq765 eq746
    | exact resolve eq746 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq791 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq765 X1 (M.op (τ (M.op x x)) (M.op X0 X0)) (τ x)
       have i₂ := eq107 x X0
       grind)
    | exact superpose eq107 eq765
    | exact resolve eq765 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq796 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq765 (M.op X1 (M.op X0 X0)) (M.op X1 X1) x
       have i₂ := eq300 X1 x X0
       grind)
    | exact superpose eq300 eq765
    | exact resolve eq765 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq837 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq796 X0 X1
       have i₂ := eq103 X1 (M.op X0 X0)
       grind)
    | exact superpose eq103 eq796
    | exact resolve eq796 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq938 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))) = (M.op (M.op X2 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq766 (M.op X1 (M.op X0 X0)) X2 (M.op x (M.op X1 X1))
       have i₂ := eq300 X1 x X0
       grind)
    | exact superpose eq300 eq766
    | exact resolve eq766 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq995 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) = (M.op (M.op X2 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq938 X0 X1 X2
       have i₂ := eq103 X1 (M.op X0 X0)
       grind)
    | exact superpose eq103 eq938
    | exact resolve eq938 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq1015 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op (M.op X2 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq995 X0 X1 X2
       have i₂ := eq837 X0 X1
       grind)
    | exact superpose eq837 eq995
    | exact resolve eq995 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq995
  have eq1318 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq767 (M.op X1 X0) X2 X0 (M.op x (M.op X1 X1))
       have i₂ := eq581 X1 X0 x
       grind)
    | exact superpose eq581 eq767
    | exact resolve eq767 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1339 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301 X0 (M.op X1 (M.op X2 X0)) x
       have i₂ := eq767 X0 x X1 X2
       grind)
    | exact superpose eq767 eq301
    | exact resolve eq301 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq1373 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1318 X0 X1 X2
       have i₂ := eq103 X1 X0
       grind)
    | exact superpose eq103 eq1318
    | exact resolve eq1318 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq1318
  have eq1435 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1373 (M.op X1 (M.op X0 X0)) X2 (M.op x (M.op X1 X1))
       have i₂ := eq300 X1 x X0
       grind)
    | exact superpose eq300 eq1373
    | exact resolve eq1373 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq2314 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq656 x y
       grind)
    | exact superpose eq656 eq16
    | (have j1 := eq656 x y
       grind)
    | exact resolve eq16 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq2848 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq116 X2 X2 X3 X4
       have i₂ := eq301 X2 X0 X1
       grind)
    | exact superpose eq301 eq116
    | exact resolve eq116 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2864 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq116 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq116 eq116
    | exact resolve eq116 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2900 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X2 (M.op X3 X4)) (M.op X1 (M.op X0 X1))) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq484 X4 X3 (M.op (M.op X2 (M.op X3 X4)) (M.op X1 (M.op X0 X1)))
       have i₂ := eq116 X1 X0 (M.op X3 X4) X2
       grind)
    | exact superpose eq116 eq484
    | exact resolve eq484 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2916 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq453 X0 X1 X2 X3
       have i₂ := eq2864 X0 X1 X0
       grind)
    | exact superpose eq2864 eq453
    | exact resolve eq453 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq2918 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op (M.op X0 X0) (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1435 X0 X1 X2
       have i₂ := eq2864 X2 X1 (M.op X0 X0)
       grind)
    | exact superpose eq2864 eq1435
    | exact resolve eq1435 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq5931 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq408 (M.op X1 X0) X2 X3
       have i₂ := eq1373 X0 X1 X1
       grind)
    | exact superpose eq1373 eq408
    | exact resolve eq408 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5966 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq301 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) X1 x
       have i₂ := eq408 X1 x X0
       grind)
    | exact superpose eq408 eq301
    | exact resolve eq301 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq6035 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq287 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op X2 X1)
       have i₂ := eq408 X1 X2 X0
       grind)
    | exact superpose eq408 eq287
    | exact resolve eq287 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq6059 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op X2 X1) (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6035 X0 X1 X2
       have i₂ := eq2864 (M.op X2 X1) X2 X1
       grind)
    | exact superpose eq2864 eq6035
    | exact resolve eq6035 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6035
  have eq6117 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5966 X0 X1
       have i₂ := eq2864 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op X1 (M.op X1 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq2864 eq5966
    | exact resolve eq5966 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5966
  have eq6138 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5931 X0 X1 X2 X3
       have i₂ := eq2864 X0 X1 X0
       grind)
    | exact superpose eq2864 eq5931
    | exact resolve eq5931 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5931
  have eq6192 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6059 X0 X1 X2
       have i₂ := eq2916 X1 X2 X1 X2
       grind)
    | exact superpose eq2916 eq6059
    | exact resolve eq6059 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6059
  have eq6246 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6117 X0 X1
       have i₂ := eq2916 (M.op X0 X0) (M.op X1 (M.op X1 X1)) (M.op X0 X0) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq2916 eq6117
    | exact resolve eq6117 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6117
  have eq6301 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6192 X0 X1 X2
       have i₂ := eq2864 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op X1 (M.op X1 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq2864 eq6192
    | exact resolve eq6192 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6192
  have eq6308 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6246 X0 X1
       have i₂ := eq2918 X0 (M.op X1 (M.op X1 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq2918 eq6246
    | exact resolve eq6246 eq2918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6246
  have eq6342 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6301 X0 X1 X2
       have i₂ := eq2916 (M.op X0 X0) (M.op X1 (M.op X1 X1)) (M.op X0 X0) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq2916 eq6301
    | exact resolve eq6301 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6301
  have eq6345 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6308 X0 X1
       have i₂ := eq1015 X0 (M.op X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq1015 eq6308
    | exact resolve eq6308 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6308
  have eq6379 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) = (M.op X0 (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6342 X0 X1 X2
       have i₂ := eq2918 X0 (M.op X1 (M.op X1 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq2918 eq6342
    | exact resolve eq6342 eq2918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2918 eq6342
  have eq6390 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6379 X0 X1 X2
       have i₂ := eq1015 X0 (M.op X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq1015 eq6379
    | exact resolve eq6379 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6379
  have eq6395 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6390 X0 X1 X2
       have i₂ := eq6345 X0 X1
       grind)
    | exact superpose eq6345 eq6390
    | exact resolve eq6390 eq6345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345 eq6390
  have eq6410 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6138 X0 X1 X2 X3
       have i₂ := eq6395 (M.op X3 X3) X0 X1
       grind)
    | exact superpose eq6395 eq6138
    | exact resolve eq6138 eq6395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6138
  have eq6420 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1))) X4) = (M.op (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1))) (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1))) (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6395 X4 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1))) X3
       have i₂ := eq116 X1 X0 X3 X2
       grind)
    | exact superpose eq116 eq6395
    | exact resolve eq6395 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6439 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6395 X2 (M.op X1 X0) (M.op X1 (M.op X1 X1))
       have i₂ := eq287 X0 X1
       grind)
    | exact superpose eq287 eq6395
    | exact resolve eq6395 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq6482 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) X3) = (M.op (M.op (M.op (M.op X1 X2) X0) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6395 X3 (M.op (M.op X1 X2) X0) X2
       have i₂ := eq481 X2 X1 X0 (M.op X1 X2)
       grind)
    | exact superpose eq481 eq6395
    | exact resolve eq6395 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq6523 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = (M.op (M.op X0 (M.op X2 X0)) (M.op X1 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1373 (M.op X0 (M.op X2 X0)) X1 X0
       have i₂ := eq6395 (M.op X1 (M.op X0 (M.op X2 X0))) X0 X2
       grind)
    | exact superpose eq6395 eq1373
    | exact resolve eq1373 eq6395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq6583 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0))))) (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq581 (M.op X0 (M.op X0 (M.op X1 X0))) X2 X3
       have i₂ := eq6395 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq6395 eq581
    | exact resolve eq581 eq6395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq6643 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X0 (M.op X0 (M.op X2 X0)))) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op X0 (M.op X2 X0))) X1
       have i₂ := eq6395 (M.op (M.op X1 (M.op X0 (M.op X0 (M.op X2 X0)))) (M.op X3 X3)) X0 X2
       grind)
    | exact superpose eq6395 eq9
    | exact resolve eq9 eq6395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6684 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0))))) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6583 X0 X1 X2 X3
       have i₂ := eq6395 X2 X0 X1
       grind)
    | exact superpose eq6395 eq6583
    | exact resolve eq6583 eq6395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6583
  have eq6707 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = (M.op (M.op X2 X0) (M.op X1 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6523 X0 X1 X2
       have i₂ := eq2864 X1 X0 (M.op X2 X0)
       grind)
    | exact superpose eq2864 eq6523
    | exact resolve eq6523 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6523
  have eq6718 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) X3) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6482 X0 X1 X2 X3
       have i₂ := eq791 (M.op X1 X2) X0
       grind)
    | exact superpose eq791 eq6482
    | exact resolve eq6482 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq6482
  have eq6749 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) (M.op X0 (M.op X0 (M.op X0 X0)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6439 X0 X1 X2
       have i₂ := eq1015 X0 X0 X1
       grind)
    | exact superpose eq1015 eq6439
    | exact resolve eq6439 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq6439
  have eq6761 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1))) X4) = (M.op (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6420 X0 X1 X2 X3 X4
       have i₂ := eq766 (M.op X0 X1) (M.op X2 X3) X1
       grind)
    | exact superpose eq766 eq6420
    | exact resolve eq6420 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq6420
  have eq6808 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq521 X0 X1
       have i₂ := eq6707 X0 X0 X1
       grind)
    | exact superpose eq6707 eq521
    | exact resolve eq521 eq6707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq6707
  have eq6830 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6749 X0 X1 X2
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq6749
    | exact resolve eq6749 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6749
  have eq6842 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1))) X4) = (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6761 X0 X1 X2 X3 X4
       have i₂ := eq1339 (M.op X0 X1) (M.op X2 X3) X1
       grind)
    | exact superpose eq1339 eq6761
    | exact resolve eq6761 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq6761
  have eq6887 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 (M.op X1 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6684 X0 X1 X2 X3
       have i₂ := eq6808 X0 X1
       grind)
    | exact superpose eq6808 eq6684
    | exact resolve eq6684 eq6808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6684 eq6808
  have eq6916 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6830 X0 X1 X2
       have i₂ := eq6718 X0 X1 X0 X2
       grind)
    | exact superpose eq6718 eq6830
    | exact resolve eq6830 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6718 eq6830
  have eq6918 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1))) X4) = (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6842 X0 X1 X2 X3 X4
       have i₂ := eq2864 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq2864 eq6842
    | exact resolve eq6842 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6842
  have eq6946 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1))) X4) = (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6918 X0 X1 X2 X3 X4
       have i₂ := eq2916 X1 X0 X1 X0
       grind)
    | exact superpose eq2916 eq6918
    | exact resolve eq6918 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6918
  have eq6952 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1))) X4) = (M.op X1 X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6946 X0 X1 X2 X3 X4
       have i₂ := eq6395 X4 X1 X0
       grind)
    | exact superpose eq6395 eq6946
    | exact resolve eq6946 eq6395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6395 eq6946
  have eq6967 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X1 (M.op X0 X1))) = (M.op X1 (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2900 X0 X1 X2 X3 X4
       have i₂ := eq6952 X0 X1 X2 (M.op X3 X4) (M.op X4 (M.op X0 X1))
       grind)
    | exact superpose eq6952 eq2900
    | exact resolve eq2900 eq6952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2900 eq6952
  have eq7202 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6916 X1 X0 X2
       have i₂ := eq6916 X1 X3 X2
       grind)
    | (have i₁ := eq6916 X0 X1 X2
       have i₂ := eq6916 X0 X0 X2
       grind)
    | exact superpose eq6916 eq6916
    | exact resolve eq6916 eq6916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6916
  have eq7832 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X0))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7202 X1 (M.op (M.op X2 X3) (M.op X0 X0)) X4 X3
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq7202
    | exact resolve eq7202 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8370 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X0 X0)) = (M.op X0 (M.op X4 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq733 X0 x X2 X3 X4
       have i₂ := eq7832 X0 x X2 (M.op X3 X4) (M.op X4 X0)
       grind)
    | exact superpose eq7832 eq733
    | exact resolve eq733 eq7832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq7832
  have eq8419 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6643 X0 x X2 X3
       have i₂ := eq8370 X3 x X0 (M.op X0 (M.op X2 X0))
       grind)
    | exact superpose eq8370 eq6643
    | exact resolve eq6643 eq8370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6643 eq8370
  have eq10186 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op (M.op X2 (M.op X3 X4)) (M.op X4 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq484 X1 X0 (M.op (M.op X2 (M.op X3 X4)) (M.op X4 (M.op X0 X1)))
       have i₂ := eq6887 X4 X3 (M.op X0 X1) X2
       grind)
    | exact superpose eq6887 eq484
    | exact resolve eq484 eq6887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq6887
  have eq10197 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op X2 (M.op X3 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10186 X0 X1 X2 X3 X4
       have i₂ := eq6967 X0 X1 (M.op X2 (M.op X3 X4)) X4 (M.op X0 X1)
       grind)
    | exact superpose eq6967 eq10186
    | exact resolve eq10186 eq6967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6967 eq10186
  have eq10259 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (M.op (M.op X2 (M.op X3 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10197 X0 X1 X2 X3 X4
       have i₂ := eq2916 X1 X0 X1 X0
       grind)
    | exact superpose eq2916 eq10197
    | exact resolve eq10197 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10197
  have eq10482 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 (M.op X1 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq116 X0 (M.op (M.op X1 X2) (M.op X3 (M.op X1 X2))) X2 X1
       have i₂ := eq8419 (M.op X1 X2) X3 X0
       grind)
    | exact superpose eq8419 eq116
    | exact resolve eq116 eq8419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq8419
  have eq10515 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X2 (M.op X3 (M.op X1 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10482 X0 X1 X2 X3
       have i₂ := eq2864 X3 X1 X2
       grind)
    | exact superpose eq2864 eq10482
    | exact resolve eq10482 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864 eq10482
  have eq13132 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7202 X2 (M.op X3 (M.op X4 X0)) X1 X0
       have i₂ := eq10515 X1 X4 X0 X3
       grind)
    | exact superpose eq10515 eq7202
    | exact resolve eq7202 eq10515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7202 eq10515
  have eq118032 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2848 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq457 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | (have i₁ := eq2848 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq457 X0 X1 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) (M.op X4 X5) X3
       grind)
    | exact superpose eq457 eq2848
    | exact resolve eq2848 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq2848
  have eq119211 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op X5 X6)))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq118032 X0 X1 x x x X5 X6
       have i₂ := eq13132 X5 X6 x x x
       grind)
    | exact superpose eq13132 eq118032
    | exact resolve eq118032 eq13132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13132 eq118032
  have eq120399 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (σ y) (M.op X0 (M.op (M.op X1 X0) (σ (M.op y y))))) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq119211 X0 X1 (σ y) (σ x)
       have i₂ := eq2314
       grind)
    | exact superpose eq2314 eq119211
    | exact resolve eq119211 eq2314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121774 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120399 x x
       have i₂ := eq102 y x x
       grind)
    | exact superpose eq102 eq120399
    | exact resolve eq120399 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120399
  have eq122072 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq121774
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq121774
    | exact resolve eq121774 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121774
  have eq122251 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq122072
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq122072
    | exact resolve eq122072 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122072
  have eq122968 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (σ (M.op y y)))) = (M.op (σ x) (M.op (σ x) (σ (M.op y y)))) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq2916 (σ x) (σ y) x x
       have i₂ := eq2314
       grind)
    | exact superpose eq2314 eq2916
    | exact resolve eq2916 eq2314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314 eq2916
  have eq124044 : (σ y) = (M.op (σ x) (M.op (σ x) (σ (M.op y y)))) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq122968 x x
       have i₂ := eq102 y x x
       grind)
    | exact superpose eq102 eq122968
    | exact resolve eq122968 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq122968
  have eq124360 : (σ y) = (M.op (σ x) (M.op (σ x) (σ (M.op x x)))) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq122251 eq124044
    | exact resolve eq124044 eq122251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122251 eq124044
  have eq124507 : (σ y) = (M.op (σ x) (σ (M.op x (M.op x x)))) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq124360
       have i₂ := eq120 x
       grind)
    | exact superpose eq120 eq124360
    | exact resolve eq124360 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq124360
  have eq124575 : (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq124507
       have i₂ := eq127 x
       grind)
    | exact superpose eq127 eq124507
    | exact resolve eq124507 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq124507
  have eq124576 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq124575
  have eq124601 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq124576
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq124576
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq124576
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq124576
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq124576 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124576
  have eq124603 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq124601
  have eq124710 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op y x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6410 X2 X1 X0 y
       have i₂ := eq124603
       grind)
    | exact superpose eq124603 eq6410
    | exact resolve eq6410 eq124603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6410
  have eq124842 : ∀ X0 X1 : G, (M.op y x) = (M.op y (M.op X0 (M.op (M.op X1 X0) (M.op y x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq119211 X0 X1 y y
       have i₂ := eq124603
       grind)
    | exact superpose eq124603 eq119211
    | exact resolve eq119211 eq124603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124603
  have eq124843 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq124842 x x
       have i₂ := eq119211 x x y x
       grind)
    | exact superpose eq119211 eq124842
    | exact resolve eq124842 eq119211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119211 eq124842
  have eq124913 : y = (M.op x (M.op x (M.op y x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq124710 x x x
       have i₂ := eq10259 y x x x x
       grind)
    | exact superpose eq10259 eq124710
    | exact resolve eq124710 eq10259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10259 eq124710
  have eq124963 : y = (M.op x (M.op x (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq124843 eq124913
    | exact resolve eq124913 eq124843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124843 eq124913
  have eq124981 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq124963
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq124963
    | exact resolve eq124963 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq124963
  have eq124982 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq124981
  have eq125010 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq124982
       grind)
    | exact superpose eq124982 eq10
    | exact resolve eq10 eq124982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124982
  have eq125130 : x = y ∨ x = y := by
    first
    | (have i₁ := eq125010
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq125010
    | exact resolve eq125010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125010
  have eq125131 : x = y := by grind
  clear eq125130
  have eq125139 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq125131
       grind)
    | exact superpose eq125131 eq16
    | exact resolve eq16 eq125131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125131
  have eq125165 : False := by grind
  exact eq125165

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X3 ∨ (k X0 X3) = (M.op X3 X0) ∨ X0 = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X2
       have i₂ := eq14 X0 X3
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X3
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X3 : G, X0 = X3 ∨ (k X0 X3) = (M.op X3 X0) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq41 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq41
    | (have j0 := eq41 X0 x x X3
       grind)
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq44 : ∀ X0 X3 : G, (k X0 X3) = (M.op X3 X0) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have j0 := eq43 X0 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq81 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq49
    | (have j0 := eq49 X0 X1
       have j1 := eq44 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq49 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq49
  have eq3691 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq282 x y
       grind)
    | exact superpose eq282 eq16
    | (have j1 := eq282 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq282 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq282 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq282 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq3752 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3691
  have eq6056 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq81 y X0 X1
       have i₂ := eq3752
       grind)
    | exact superpose eq3752 eq81
    | exact resolve eq81 eq3752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3752
  have eq6120 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6056 x x
       have i₂ := eq81 x x x
       grind)
    | exact superpose eq81 eq6056
    | exact resolve eq6056 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq6056
  have eq6121 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6120
  have eq6129 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6121
       grind)
    | exact superpose eq6121 eq10
    | exact resolve eq10 eq6121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6121
  have eq6158 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6129
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6129
    | exact resolve eq6129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6129
  have eq6159 : x = y := by grind
  clear eq6158
  have eq8426 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6159
       grind)
    | exact superpose eq6159 eq16
    | exact resolve eq16 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6159
  have eq8427 : False := by grind
  exact eq8427

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X3 ∨ (k X0 X3) = (M.op X3 X0) ∨ X0 = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X2
       have i₂ := eq14 X0 X3
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X3
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X3 : G, X0 = X3 ∨ (k X0 X3) = (M.op X3 X0) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq41 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq41
    | (have j0 := eq41 X0 x x X3
       grind)
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq44 : ∀ X0 X3 : G, (k X0 X3) = (M.op X3 X0) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have j0 := eq43 X0 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq81 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq49
    | (have j0 := eq49 X0 X1
       have j1 := eq44 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq49 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq49
  have eq3671 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq282 x y
       grind)
    | exact superpose eq282 eq16
    | (have j1 := eq282 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq282 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq282 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq282 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq3732 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3671
  have eq6035 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq81 y X0 X1
       have i₂ := eq3732
       grind)
    | exact superpose eq3732 eq81
    | exact resolve eq81 eq3732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732
  have eq6099 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6035 x x
       have i₂ := eq81 x x x
       grind)
    | exact superpose eq81 eq6035
    | exact resolve eq6035 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq6035
  have eq6100 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6099
  have eq6108 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6100
       grind)
    | exact superpose eq6100 eq10
    | exact resolve eq10 eq6100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6100
  have eq6137 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6108
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6108
    | exact resolve eq6108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108
  have eq6138 : x = y := by grind
  clear eq6137
  have eq8409 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6138
       grind)
    | exact superpose eq6138 eq16
    | exact resolve eq16 eq6138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6138
  have eq8410 : False := by grind
  exact eq8410

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq45
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq54 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq85 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq90 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq86
  have eq91 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq90
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
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
  clear eq85
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq92
    | exact resolve eq92 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq22 eq98
    | exact resolve eq98 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq124 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq490 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq57 X0 X0
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X1 X0)
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq55
    | exact resolve eq55 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq495 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq514 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq56 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (M.op X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 (σ X0) X1 X2 X3
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq56
    | exact resolve eq56 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1812 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 (M.op X0 X0))
       have i₂ := eq514 X0 X0 X0
       grind)
    | exact superpose eq514 eq54
    | exact resolve eq54 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq2032 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq490 X0
       have i₂ := eq1812 X0
       grind)
    | exact superpose eq1812 eq490
    | exact resolve eq490 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq2060 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1812 eq492
    | exact resolve eq492 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812
  have eq2070 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq492 eq2060
    | exact resolve eq2060 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq2060
  have eq2105 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq54 eq2032
    | exact resolve eq2032 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2032
  have eq4806 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq495 (σ X0) (σ X0) (σ (M.op X0 X0)) (M.op x x)
       have i₂ := eq533 X0 x x (σ X0)
       grind)
    | exact superpose eq533 eq495
    | exact resolve eq495 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq533
  have eq4822 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4806 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq4806
    | exact resolve eq4806 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq4806
  have eq17985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq17986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq28 eq17985
    | exact resolve eq17985 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17985
  have eq17997 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq17986
       have r₂ := eq29
       grind)
    | exact resolve eq17986 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17986
  have eq18003 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17997 eq124
    | exact resolve eq124 eq17997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq17997
  have eq18100 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq18003
    | exact resolve eq18003 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18003
  have eq18101 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18100
  have eq18157 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2105 y
       have i₂ := eq18101
       grind)
    | exact superpose eq18101 eq2105
    | exact resolve eq2105 eq18101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105 eq18101
  have eq18205 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18157
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq18157
    | exact resolve eq18157 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18157
  have eq18242 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18205 eq31
    | exact resolve eq31 eq18205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq18205
  have eq18381 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq18242
    | exact resolve eq18242 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18242
  have eq18382 : x = (M.op x y) ∨ x = y := by grind
  clear eq18381
  have eq18535 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq18382 eq22
    | exact resolve eq22 eq18382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18611 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq18382 eq2070
    | exact resolve eq2070 eq18382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070 eq18382
  have eq18630 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq18611
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq18611
    | exact resolve eq18611 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18611
  have eq18678 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq18535
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18535
    | exact resolve eq18535 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18535
  have eq18693 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq18678 eq28
    | exact resolve eq28 eq18678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18678
  have eq18868 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4822 y
       have i₂ := eq18630
       grind)
    | exact superpose eq18630 eq4822
    | exact resolve eq4822 eq18630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4822 eq18630
  have eq18913 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18868
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq18868
    | exact resolve eq18868 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18868
  have eq18941 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq22 eq18913
    | exact resolve eq18913 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18913
  have eq19232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18941 eq18693
    | exact resolve eq18693 eq18941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18693 eq18941
  have eq19263 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq19232
  have eq19270 : x = y := by
    first
    | (have r₁ := eq19263
       have r₂ := eq29
       grind)
    | exact resolve eq19263 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19263
  have eq19410 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq19270
       grind)
    | exact superpose eq19270 eq20
    | exact resolve eq20 eq19270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq19411 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq19270
       grind)
    | exact superpose eq19270 eq26
    | exact resolve eq26 eq19270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq19270
  have eq19560 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19411
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19411
    | exact resolve eq19411 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19411
  have eq19584 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19560 eq28
    | exact resolve eq28 eq19560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19560
  have eq19962 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19584 eq69
    | exact resolve eq69 eq19584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq19584
  have eq20080 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19962
       have i₂ := eq19410
       grind)
    | exact superpose eq19410 eq19962
    | exact resolve eq19962 eq19410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19410 eq19962
  have eq20110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20080 eq15
    | exact resolve eq15 eq20080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20080
  have eq20160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq20110
    | exact resolve eq20110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20110
  have eq20175 : False := by grind
  exact eq20175

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq43 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq15
    | exact resolve eq15 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq57
    | exact resolve eq57 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq57
  have eq80 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X0) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq80
    | (have j0 := eq80 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq80 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq250 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq148
       have i₂ := eq80 y x
       grind)
    | exact superpose eq80 eq148
    | (have j1 := eq80 (σ x) (σ y)
       grind)
    | (have r₁ := eq148
       have r₂ := eq80 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq148
       have r₂ := eq80 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq148 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq148
  have eq253 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq250
  have eq288 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq253
       grind)
    | exact superpose eq253 eq16
    | exact resolve eq16 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq289 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq288
       have r₂ := eq66 x
       grind)
    | exact resolve eq288 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq329 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq289
       grind)
    | exact superpose eq289 eq10
    | exact resolve eq10 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq350 : x = y := by
    first
    | (have i₁ := eq329
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq329
    | exact resolve eq329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq398 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq350
       grind)
    | exact superpose eq350 eq16
    | exact resolve eq16 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq399 : False := by grind
  exact eq399

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X2) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq23
  have eq69 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X3 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)))) = (M.op X3 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X4 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)) X3 X2
       have i₂ := eq9 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X3 X0) X2))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq55 x X2 X0 X3
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq55 X1 (M.op X0 X2) X0 x
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X2 (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) X1
       have i₂ := eq73 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq73 eq73
    | exact resolve eq73 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1 X4
       have i₂ := eq73 X1 X0 X2
       grind)
    | exact superpose eq73 eq55
    | exact resolve eq55 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X2 X1) X0) X1 x
       grind)
    | exact superpose eq9 eq91
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq113 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op (M.op X2 X1) (M.op (M.op X4 (M.op X2 X1)) (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op X1 (M.op X1 X0)) (M.op X2 X1) X4
       have i₂ := eq77 X1 X2 X0
       grind)
    | exact superpose eq77 eq55
    | exact resolve eq55 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X4 (M.op X1 (M.op X1 X0))) X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq55 (M.op x X1) X3 (M.op X1 (M.op X1 X0)) X4
       have i₂ := eq77 X1 x X0
       grind)
    | exact superpose eq77 eq55
    | exact resolve eq55 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq77
  have eq118 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq114 X0 X1 X3 x
       have i₂ := eq88 X3 X1 (M.op X1 X0) x
       grind)
    | exact superpose eq88 eq114
    | exact resolve eq114 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq119 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X1 (M.op X1 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X0 X1 X2 X3 x
       have i₂ := eq88 (M.op X1 (M.op X1 X0)) X2 X1 x
       grind)
    | exact superpose eq88 eq113
    | exact resolve eq113 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq113
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq272 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq272
    | (have j0 := eq272 (σ X0)
       grind)
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1165 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1190 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq2173 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) = (M.op (M.op X5 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq96 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X1))) X3 X5 X2
       have i₂ := eq119 X1 (M.op X2 X3) X0 X4
       grind)
    | exact superpose eq119 eq96
    | exact resolve eq96 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq119
  have eq2182 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) = (M.op (M.op X5 X3) (M.op X3 (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 X3) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2173 X0 X1 X2 X3 X4 X5
       have i₂ := eq118 X3 X2 (M.op (M.op X2 X3) X1)
       grind)
    | exact superpose eq118 eq2173
    | exact resolve eq2173 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq2173
  have eq2303 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2182 X0 X1 X2 X3 X4 x
       have i₂ := eq69 X2 X1 X2 X3 x
       grind)
    | exact superpose eq69 eq2182
    | exact resolve eq2182 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2182
  have eq2452 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X0))) X2) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2303 X4 X2 X1 X1 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq2303 X0 X1 X0 X0 X4
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq2303
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq2303 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2616 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2452 X0 X1 X2 x x
       have i₂ := eq2303 x X2 X0 X0 x
       grind)
    | exact superpose eq2303 eq2452
    | (have j0 := eq2452 X0 X1 X2 x x
       grind)
    | exact resolve eq2452 eq2303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2303 eq2452
  have eq14272 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq1190
  have eq14317 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14272
  have eq15750 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2
    grind
  clear eq2616
  have eq15803 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq15750 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15750
  have eq16125 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X3 X0) (M.op X2 X1))) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 X3
       have i₂ := eq15803 X1 X2 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq15803 X0 X1 X2
       grind)
    | exact superpose eq15803 eq9
    | (have j1 := eq15803 X0 X2 X0
       grind)
    | exact resolve eq9 eq15803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15803
  have eq22690 : ∀ X0 X2 : G, X0 = X2 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq1165 X2 X0 x
       have i₂ := eq16125 X0 X2 X2 x
       grind)
    | exact superpose eq16125 eq1165
    | (have j0 := eq1165 X2 X0 X2
       have j1 := eq16125 X0 x X2 x
       grind)
    | exact resolve eq1165 eq16125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165 eq16125
  have eq22746 : ∀ X0 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X2 ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have j0 := eq22690 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22690
  have eq22869 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq22746
  have eq23052 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq22869 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22869
  have eq23068 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23052 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq23052
    | (have j0 := eq23052 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq23052 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23079 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq23052 X0 (τ X1)
       grind)
    | exact superpose eq23052 eq19
    | (have j1 := eq23052 (k (σ X0) X1) (σ (M.op (τ X1) X0))
       grind)
    | exact resolve eq19 eq23052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq23052
  have eq23508 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23079 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23079
    | exact resolve eq23079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23079
  have eq23599 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23508 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq23508
    | (have j0 := eq23508 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq23508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23508
  have eq23890 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23068 y x
       grind)
    | exact superpose eq23068 eq16
    | (have j1 := eq23068 x y
       grind)
    | exact resolve eq16 eq23068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23068
  have eq24002 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23890
       have i₂ := eq23599 x y
       grind)
    | exact superpose eq23599 eq23890
    | (have j1 := eq23599 (σ x) (σ y)
       grind)
    | (have r₁ := eq23890
       have r₂ := eq23599 x y
       grind)
    | (have r₁ := eq23890
       have r₂ := eq23599 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq23890
       have r₂ := eq23599 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq23890 eq23599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23599 eq23890
  have eq24005 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq24002
  have eq24013 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24005
       grind)
    | exact superpose eq24005 eq10
    | exact resolve eq10 eq24005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24005
  have eq24057 : x = y ∨ x = y := by
    first
    | (have i₁ := eq24013
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24013
    | exact resolve eq24013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24013
  have eq24058 : x = y := by grind
  clear eq24057
  have eq24060 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24058
       grind)
    | exact superpose eq24058 eq16
    | exact resolve eq16 eq24058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24058
  have eq24061 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24060
       have i₂ := eq274 x
       grind)
    | exact superpose eq274 eq24060
    | (have j1 := eq274 x
       grind)
    | exact resolve eq24060 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq26760 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24061
       have i₂ := eq272 x
       grind)
    | exact superpose eq272 eq24061
    | (have j1 := eq272 (σ x)
       grind)
    | exact resolve eq24061 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26761 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq26760
  have eq26773 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq26761
       grind)
    | exact superpose eq26761 eq57
    | exact resolve eq57 eq26761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq26886 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26773
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26773
    | exact resolve eq26773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26773
  have eq27532 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26886
       have i₂ := eq26761
       grind)
    | exact superpose eq26761 eq26886
    | exact resolve eq26886 eq26761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26761 eq26886
  have eq27563 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq27532
  have eq27564 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq27563
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27563
    | exact resolve eq27563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27563
  have eq27570 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq272 x
       have i₂ := eq27564
       grind)
    | exact superpose eq27564 eq272
    | (have j0 := eq272 x
       grind)
    | exact resolve eq272 eq27564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq27564
  have eq27571 : x = (M.op x x) := by grind
  clear eq27570
  have eq27595 : ∀ X0 : G, (M.op X0 x) = (k x X0) ∨ (M.op X0 x) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq14317 x x
       have i₂ := eq27571
       grind)
    | exact superpose eq27571 eq14317
    | (have j0 := eq14317 x X0
       grind)
    | exact resolve eq14317 eq27571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14317
  have eq27665 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq27595 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27595
  have eq27721 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24061
       have i₂ := eq27665 x
       grind)
    | exact superpose eq27665 eq24061
    | exact resolve eq24061 eq27665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24061 eq27665
  have eq27738 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq27721
  have eq27764 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24060
       have i₂ := eq27738
       grind)
    | exact superpose eq27738 eq24060
    | exact resolve eq24060 eq27738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24060 eq27738
  have eq27892 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq27764
       have i₂ := eq27571
       grind)
    | exact superpose eq27571 eq27764
    | exact resolve eq27764 eq27571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27571 eq27764
  have eq27893 : False := by grind
  exact eq27893

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq54 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq55 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  clear eq37
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq108
    | (have j0 := eq108 (σ X0)
       grind)
    | exact resolve eq108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq44
    | (have j1 := eq108 x
       grind)
    | exact resolve eq44 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq498 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq501 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq6215 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq381 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq69942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq69942
    | exact resolve eq69942 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69942
  have eq69954 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq69943
       have r₂ := eq28
       grind)
    | exact resolve eq69943 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69943
  have eq69956 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq69954
    | exact resolve eq69954 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69954
  have eq70013 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq69956 eq498
    | exact resolve eq498 eq69956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69956
  have eq70085 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq501 eq70013
    | exact resolve eq70013 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70013
  have eq70121 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq70085
  have eq70249 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq70121
    | exact resolve eq70121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70121
  have eq70550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq70249 eq93
    | exact resolve eq93 eq70249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq70249
  have eq70558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq70550
  have eq70560 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq70558
       have r₂ := eq28
       grind)
    | exact resolve eq70558 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70558
  have eq70873 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq498 x X0 x
       have i₂ := eq70560
       grind)
    | exact superpose eq70560 eq498
    | exact resolve eq498 eq70560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70560
  have eq70945 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq500 eq70873
    | exact resolve eq70873 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq70873
  have eq70982 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq70945
  have eq71110 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70982
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70982
    | exact resolve eq70982 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70982
  have eq71159 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq71110
       grind)
    | exact superpose eq71110 eq72
    | exact resolve eq72 eq71110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq71110
  have eq71177 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq71159
    | exact resolve eq71159 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71159
  have eq71211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq71177 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq71177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq71211
    | exact resolve eq71211 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71211
  have eq71225 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq71214
       have r₂ := eq28
       grind)
    | exact resolve eq71214 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71214
  have eq71227 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq71225
    | exact resolve eq71225 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71225
  have eq101859 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq71227 eq498
    | exact resolve eq498 eq71227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq71227
  have eq101950 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq501 eq101859
    | exact resolve eq101859 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq101859
  have eq101951 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq101950
  have eq102735 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq101951
  have eq102889 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq102735
    | exact resolve eq102735 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102735
  have eq102946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq102889 eq71177
    | exact resolve eq71177 eq102889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71177 eq102889
  have eq102948 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq102946
  have eq102956 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq102948
       have r₂ := eq28
       grind)
    | exact resolve eq102948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102948
  have eq104295 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq102956 eq30
    | exact resolve eq30 eq102956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq102956
  have eq104457 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq104295
    | exact resolve eq104295 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq104295
  have eq104458 : x = y := by grind
  clear eq104457
  have eq104459 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq104458
       grind)
    | exact superpose eq104458 eq19
    | exact resolve eq19 eq104458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq104460 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq104458
       grind)
    | exact superpose eq104458 eq25
    | exact resolve eq25 eq104458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq104458
  have eq104625 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq104460
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq104460
    | exact resolve eq104460 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104460
  have eq104626 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq104625 eq27
    | exact resolve eq27 eq104625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq104625
  have eq104797 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq385
       have i₂ := eq104459
       grind)
    | exact superpose eq104459 eq385
    | exact resolve eq385 eq104459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq104831 : (k (M.op x y) x) = (M.op x (M.op x y)) := by grind
  have eq104989 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq104797
    | exact resolve eq104797 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104797
  have eq105045 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq107884 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104989 eq108
    | (have j0 := eq108 (σ x)
       grind)
    | exact resolve eq108 eq104989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq107885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104626 eq107884
    | exact resolve eq107884 eq104626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107884
  have eq107897 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq107885
       have r₂ := eq28
       grind)
    | exact resolve eq107885 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107885
  have eq107903 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104626 eq107897
    | exact resolve eq107897 eq104626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107897
  have eq107950 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107903 eq105045
    | exact resolve eq105045 eq107903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105045 eq107903
  have eq107956 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104626 eq107950
    | exact resolve eq107950 eq104626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107950
  have eq109335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107956 eq104989
    | exact resolve eq104989 eq107956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104989 eq107956
  have eq109339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq109335
  have eq109343 : x = (M.op x y) := by
    first
    | (have r₁ := eq109339
       have r₂ := eq28
       grind)
    | exact resolve eq109339 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109339
  have eq109351 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq109343 eq21
    | exact resolve eq21 eq109343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq109496 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq109343 eq104831
    | exact resolve eq104831 eq109343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104831
  have eq109504 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq109496
       have i₂ := eq104459
       grind)
    | exact superpose eq104459 eq109496
    | exact resolve eq109496 eq104459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104459 eq109496
  have eq109607 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq109351
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq109351
    | exact resolve eq109351 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109351
  have eq109611 : x = (k x x) := by
    first
    | exact superpose eq109343 eq109504
    | exact resolve eq109504 eq109343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109343 eq109504
  have eq109995 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6215 x
       have i₂ := eq109611
       grind)
    | exact superpose eq109611 eq6215
    | (have j0 := eq6215 x
       grind)
    | exact resolve eq6215 eq109611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6215 eq109611
  have eq109999 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq109995
  have eq110009 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq109999
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq109999
    | exact resolve eq109999 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq109999
  have eq110021 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104626 eq110009
    | exact resolve eq110009 eq104626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104626 eq110009
  have eq110032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109607 eq110021
    | exact resolve eq110021 eq109607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109607 eq110021
  have eq110041 : False := by grind
  exact eq110041
