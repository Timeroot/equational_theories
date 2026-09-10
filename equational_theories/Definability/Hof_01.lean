import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq71
  have eq84 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq84
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq148 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq369 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
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
  clear eq369
  have eq540 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq541 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq540 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq844 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq847 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq375
    | exact resolve eq375 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq375
    | exact resolve eq375 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq958 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op x X0)
       have i₂ := eq844 x X0
       grind)
    | exact superpose eq844 eq50
    | exact resolve eq50 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq963 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op sF2 x)
       have i₂ := eq844 sF2 x
       grind)
    | exact superpose eq844 eq51
    | exact resolve eq51 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3431 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq541 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq541
    | (have j0 := eq541 (τ X0)
       grind)
    | exact resolve eq541 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3439 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3431 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3431
    | (have j0 := eq3431 X0
       grind)
    | exact resolve eq3431 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3431
  have eq3445 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3439 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3439
    | (have j0 := eq3439 X0
       grind)
    | exact resolve eq3439 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439
  have eq6105 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq148 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq148
    | (have j0 := eq148 x
       grind)
    | exact resolve eq148 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq6139 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6105
  have eq6142 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6139
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6139
    | exact resolve eq6139 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq6139
  have eq22358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22358
    | exact resolve eq22358 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22358
  have eq22376 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22365
       have r₂ := eq28
       grind)
    | exact resolve eq22365 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22365
  have eq22401 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  have eq22434 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22376 eq844
    | exact resolve eq844 eq22376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22376
  have eq22440 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22434
    | exact resolve eq22434 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22434
  have eq22466 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq22440
  have eq22575 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22466 eq56
    | exact resolve eq56 eq22466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22466
  have eq22618 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq22575
    | exact resolve eq22575 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22575
  have eq22621 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3445 x
       grind)
    | (have r₁ := eq22618
       have r₂ := eq3445 x
       grind)
    | exact resolve eq22618 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22618
  have eq22622 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq22621
       grind)
    | exact superpose eq22621 eq79
    | exact resolve eq79 eq22621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq22681 : x ≠ y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22621
  have eq22686 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22622
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22622
    | exact resolve eq22622 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22622
  have eq25827 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22686
       have r₂ := eq22681
       grind)
    | exact resolve eq22686 eq22681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22681 eq22686
  have eq25830 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6142 eq25827
    | exact resolve eq25827 eq6142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6142 eq25827
  have eq29052 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25830 eq844
    | exact resolve eq844 eq25830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25830
  have eq29063 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq29052
    | exact resolve eq29052 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29052
  have eq29064 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29063
  have eq29099 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29064
  have eq29180 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29099 eq56
    | exact resolve eq56 eq29099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29099
  have eq29243 : x = (k x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq29180
    | exact resolve eq29180 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29180
  have eq29246 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3445 x
       grind)
    | (have r₁ := eq29243
       have r₂ := eq3445 x
       grind)
    | exact resolve eq29243 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29243
  have eq29267 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29246
  have eq29365 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq541 x
       have i₂ := eq29267
       grind)
    | exact superpose eq29267 eq541
    | (have j0 := eq541 x
       grind)
    | exact resolve eq541 eq29267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq29267
  have eq29380 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29365
  have eq29399 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29380
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29380
    | exact resolve eq29380 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29380
  have eq29469 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29399 eq48
    | exact resolve eq48 eq29399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq29486 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29399 eq963
    | exact resolve eq963 eq29399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963 eq29399
  have eq29562 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq850 eq29486
    | exact resolve eq29486 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq29486
  have eq29844 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29562 eq29469
    | exact resolve eq29469 eq29562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29469 eq29562
  have eq29885 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29844
  have eq29886 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq29885
    | exact resolve eq29885 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29885
  have eq29887 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29886
  have eq29888 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq29887 eq28
    | exact resolve eq28 eq29887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq29887
  have eq58861 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22401 eq96
    | exact resolve eq96 eq22401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq22401
  have eq58880 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq58861
  have eq58890 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq58880
       have r₂ := eq29888
       grind)
    | exact resolve eq58880 eq29888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58880
  have eq58944 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq58890
  have eq59258 : (τ (σ x)) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq58944 eq56
    | exact resolve eq56 eq58944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq58944
  have eq59325 : x = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq59258
    | exact resolve eq59258 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq59258
  have eq59328 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq3445 x
       grind)
    | (have r₁ := eq59325
       have r₂ := eq3445 x
       grind)
    | exact resolve eq59325 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445 eq59325
  have eq59396 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq844 x x
       have i₂ := eq59328
       grind)
    | exact superpose eq59328 eq844
    | exact resolve eq844 eq59328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq59328
  have eq59413 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59396
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59396
    | exact resolve eq59396 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59396
  have eq59419 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq59413
       grind)
    | exact superpose eq59413 eq47
    | exact resolve eq47 eq59413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq59436 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq958 x
       have i₂ := eq59413
       grind)
    | exact superpose eq59413 eq958
    | exact resolve eq958 eq59413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq59413
  have eq59509 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq847 eq59436
    | exact resolve eq59436 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847 eq59436
  have eq60112 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq59509 eq59419
    | exact resolve eq59419 eq59509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59419 eq59509
  have eq60159 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq60112
  have eq60160 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq60159
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60159
    | exact resolve eq60159 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq60159
  have eq60161 : y = (M.op x y) := by grind
  clear eq60160
  have eq60162 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq60161 eq21
    | exact resolve eq21 eq60161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq60161
  have eq60441 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq60162
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq60162
    | exact resolve eq60162 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq60162
  have eq60442 : False := by grind
  exact eq60442

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  clear eq23
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
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq75
    | (have j0 := eq75 (σ x) (σ X0)
       grind)
    | exact resolve eq75 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq45
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq45 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq119 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq120 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq429 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq434 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq429 (M.op X0 X1)
       grind)
    | exact superpose eq429 eq53
    | exact resolve eq53 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq440 : (σ y) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq434
    | (have j0 := eq434 (σ x) (σ y)
       grind)
    | exact resolve eq434 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq108 eq75
    | (have j0 := eq75 (σ x) (σ y)
       grind)
    | exact resolve eq75 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq718
    | exact resolve eq718 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq722 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq719
       have r₂ := eq28
       grind)
    | exact resolve eq719 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq726 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq722 eq14
    | exact resolve eq14 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq722 eq429
    | exact resolve eq429 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  have eq738 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq733 eq14
    | exact resolve eq14 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq773 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq722 eq726
    | exact resolve eq726 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq781 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq773
  have eq831 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq726 eq738
    | exact resolve eq738 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq832 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq781 eq738
    | exact resolve eq738 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq781
  have eq840 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq832
  have eq841 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq831 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq844 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq840
    | exact resolve eq840 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq871 : ∀ X0 : G, x = (M.op (M.op y (M.op x X0)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq844
       grind)
    | exact superpose eq844 eq14
    | exact resolve eq14 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq429 x
       have i₂ := eq844
       grind)
    | exact superpose eq844 eq429
    | exact resolve eq429 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq881
       grind)
    | exact superpose eq881 eq14
    | exact resolve eq14 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq949 : x = (M.op (M.op y y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq871 x
       have i₂ := eq844
       grind)
    | exact superpose eq844 eq871
    | exact resolve eq871 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq871
  have eq957 : x = (M.op (M.op y y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq949
  have eq1008 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq886 y
       have i₂ := eq957
       grind)
    | exact superpose eq957 eq886
    | exact resolve eq886 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq957
  have eq1016 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1008
  have eq1020 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1016
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1016
    | exact resolve eq1016 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1033 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1020 eq28
    | exact resolve eq28 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1871 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq734 eq108
    | exact resolve eq108 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1874 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1871
  have eq1896 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1874 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1874
       grind)
    | exact resolve eq13 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq1897 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1896 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896
  have eq2055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1897 eq108
    | exact resolve eq108 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq2066 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2055
  have eq2072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq2066
    | exact resolve eq2066 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066
  have eq2074 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2072
       have r₂ := eq28
       grind)
    | exact resolve eq2072 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq2087 : ∀ X0 : G, x = (M.op (M.op y (M.op x X0)) x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq2074
       grind)
    | exact superpose eq2074 eq14
    | exact resolve eq14 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2097 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq429 x
       have i₂ := eq2074
       grind)
    | exact superpose eq2074 eq429
    | exact resolve eq429 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2154 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq14
    | exact resolve eq14 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097
  have eq2240 : x = (M.op (M.op y y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2087 x
       have i₂ := eq2074
       grind)
    | exact superpose eq2074 eq2087
    | exact resolve eq2087 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074 eq2087
  have eq2252 : x = (M.op (M.op y y) x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2240
  have eq2390 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2154 y
       have i₂ := eq2252
       grind)
    | exact superpose eq2252 eq2154
    | exact resolve eq2154 eq2252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154 eq2252
  have eq2399 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2390
  have eq2404 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2399
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2399
    | exact resolve eq2399 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq2406 : y = (M.op x y) := by
    first
    | (have r₁ := eq2404
       have r₂ := eq1033
       grind)
    | exact resolve eq2404 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq2404
  have eq2407 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2406 eq21
    | exact resolve eq21 eq2406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2463 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2407
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2407
    | exact resolve eq2407 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407
  have eq2464 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2463 eq27
    | exact resolve eq27 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2473 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2463 eq108
    | exact resolve eq108 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq2478 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq2463 eq440
    | exact resolve eq440 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq2568 : (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq92
    | (have j0 := eq92 (M.op x y)
       grind)
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq92
  have eq2593 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2464 eq2568
    | exact resolve eq2568 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568
  have eq2617 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq46 eq2593
    | exact resolve eq2593 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq2593
  have eq2649 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2478 eq14
    | exact resolve eq14 eq2478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq2804 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2473 eq2617
    | exact resolve eq2617 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq2809 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2804
       have r₂ := eq28
       grind)
    | exact resolve eq2804 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq2857 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2809 eq841
    | exact resolve eq841 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq2809
  have eq2876 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq2857
  have eq2882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2464 eq2876
    | exact resolve eq2876 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2876
  have eq2888 : y = (M.op x x) := by
    first
    | (have r₁ := eq2882
       have r₂ := eq28
       grind)
    | exact resolve eq2882 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882
  have eq3041 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (k x y) := by
    intro X0
    first
    | (have i₁ := eq120 x x
       have i₂ := eq2888
       grind)
    | exact superpose eq2888 eq120
    | exact resolve eq120 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq2888
  have eq4596 : y ≠ (M.op x y) ∨ y = (k x y) := by grind
  clear eq3041
  have eq4597 : y ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq4596
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4596
    | exact resolve eq4596 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4596
  have eq4616 : y = (k x y) := by
    first
    | (have r₁ := eq4597
       have r₂ := eq2406
       grind)
    | exact resolve eq4597 eq2406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2406 eq4597
  have eq4643 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq4616
       grind)
    | exact superpose eq4616 eq45
    | exact resolve eq45 eq4616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4616
  have eq4645 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2463 eq4643
    | exact resolve eq4643 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643
  have eq4646 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4645
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4645
    | exact resolve eq4645 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4645
  have eq4647 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2463 eq4646
    | exact resolve eq4646 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463 eq4646
  have eq4678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4647 eq2617
    | exact resolve eq2617 eq4647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617 eq4647
  have eq4683 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq4678
       have r₂ := eq28
       grind)
    | exact resolve eq4678 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4678
  have eq4695 : (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq4683 eq55
    | exact resolve eq55 eq4683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq4713 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq4683 eq429
    | exact resolve eq429 eq4683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq4683
  have eq4776 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq4695 eq2649
    | exact resolve eq2649 eq4695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649 eq4695
  have eq4784 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq4713 eq4776
    | exact resolve eq4776 eq4713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4713 eq4776
  have eq4786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2464 eq4784
    | exact resolve eq4784 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464 eq4784
  have eq4787 : False := by grind
  exact eq4787

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq17
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54
    | (have j0 := eq54 (σ X0) (σ X1)
       grind)
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4) X0) X5) X4) X5) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X4 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0 X5
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 X1) X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq124 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 x y
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq65 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq65 X1 X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq135 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq133 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq133 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq332 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq54 x y
       grind)
    | exact superpose eq54 eq124
    | (have j1 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq124 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq335 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq332
  have eq336 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq335
       grind)
    | exact superpose eq335 eq9
    | exact resolve eq9 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq135 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq135
    | (have j0 := eq135 (τ X0) X1
       grind)
    | exact resolve eq135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq135
  have eq548 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq551 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq548
    | (have j0 := eq548 X0 X1
       grind)
    | exact resolve eq548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq597 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq551 (τ X0) X1
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq551
    | (have j0 := eq551 (τ X0) X1
       grind)
    | exact resolve eq551 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq551
  have eq755 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq91
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq773 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq755 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq755
    | exact resolve eq755 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq1957 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq97 x X0 y
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq97
    | exact resolve eq97 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq336
  have eq2046 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1957 y
       have i₂ := eq335
       grind)
    | exact superpose eq335 eq1957
    | exact resolve eq1957 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq2092 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2046
  have eq2148 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1957 y
       have i₂ := eq2092
       grind)
    | exact superpose eq2092 eq1957
    | exact resolve eq1957 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957 eq2092
  have eq2185 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2148
  have eq2337 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq2185
       grind)
    | exact superpose eq2185 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq2185
       grind)
    | exact resolve eq12 eq2185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185
  have eq2373 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337
  have eq4055 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq124
       have i₂ := eq2373 x
       grind)
    | exact superpose eq2373 eq124
    | exact resolve eq124 eq2373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq2373
  have eq4056 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4055
  have eq4057 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4056
  have eq4060 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4057
       grind)
    | exact superpose eq4057 eq16
    | exact resolve eq16 eq4057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4063 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq4057
       grind)
    | exact superpose eq4057 eq9
    | exact resolve eq9 eq4057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4110 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq773 (σ x) (σ y)
       have i₂ := eq4057
       grind)
    | exact superpose eq4057 eq773
    | exact resolve eq773 eq4057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4139 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4063 X0
       have i₂ := eq773 (σ x) X0
       grind)
    | (have i₁ := eq4063 X0
       have i₂ := eq773 (σ x) (M.op (σ x) X0)
       grind)
    | exact superpose eq773 eq4063
    | exact resolve eq4063 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4063
  have eq4214 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq4110
       grind)
    | exact superpose eq4110 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq4110
       grind)
    | exact resolve eq12 eq4110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4215 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ x) X0
       have i₂ := eq4110
       grind)
    | exact superpose eq4110 eq9
    | exact resolve eq9 eq4110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4260 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq4214 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214
  have eq4284 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4215 X0
       have i₂ := eq773 (σ x) X0
       grind)
    | (have i₁ := eq4215 X0
       have i₂ := eq773 (σ x) (M.op (σ x) X0)
       grind)
    | exact superpose eq773 eq4215
    | exact resolve eq4215 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq4215
  have eq4409 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4260 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq4260
    | exact resolve eq4260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4424 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq597 (σ x) X0
       have i₂ := eq4260 (σ x)
       grind)
    | exact superpose eq4260 eq597
    | (have j0 := eq597 (σ x) X0
       grind)
    | exact resolve eq597 eq4260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq4260
  have eq4469 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq4424 X0
       have i₂ := eq4110
       grind)
    | exact superpose eq4110 eq4424
    | (have j0 := eq4424 X0
       grind)
    | exact resolve eq4424 eq4110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4424
  have eq4470 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | (have j0 := eq4469 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4469
  have eq4478 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq4470 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4470
    | exact resolve eq4470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470
  have eq4683 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4139 (σ x)
       have i₂ := eq4110
       grind)
    | exact superpose eq4110 eq4139
    | exact resolve eq4139 eq4110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq4781 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4683
       have i₂ := eq4057
       grind)
    | exact superpose eq4057 eq4683
    | exact resolve eq4683 eq4057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4057 eq4683
  have eq4788 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4781
       grind)
    | exact superpose eq4781 eq10
    | exact resolve eq10 eq4781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4781
  have eq4842 : x = y := by
    first
    | (have i₁ := eq4788
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4788
    | exact resolve eq4788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4788
  have eq4865 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4060
       have i₂ := eq4842
       grind)
    | exact superpose eq4842 eq4060
    | exact resolve eq4060 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060 eq4842
  have eq5228 : ∀ X3 : G, (M.op (M.op (M.op (M.op (σ x) (σ x)) X3) (σ x)) X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq92 (σ x) x x x (σ x) X3
       have i₂ := eq4284 (M.op (M.op (M.op x (σ x)) (M.op x x)) x)
       grind)
    | exact superpose eq4284 eq92
    | exact resolve eq92 eq4284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq5291 : ∀ X3 : G, (M.op (M.op (M.op (σ x) X3) (σ x)) X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq5228 X3
       have i₂ := eq4110
       grind)
    | exact superpose eq4110 eq5228
    | exact resolve eq5228 eq4110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4110 eq5228
  have eq5294 : ∀ X3 : G, (M.op (σ x) X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq5291 X3
       have i₂ := eq4284 X3
       grind)
    | exact superpose eq4284 eq5291
    | exact resolve eq5291 eq4284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291
  have eq5307 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4284 X0
       have i₂ := eq5294 X0
       grind)
    | exact superpose eq5294 eq4284
    | exact resolve eq4284 eq5294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4284 eq5294
  have eq7873 : ∀ X0 : G, (σ x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq4409 X0
       have i₂ := eq5307 (σ X0)
       grind)
    | exact superpose eq5307 eq4409
    | exact resolve eq4409 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4409 eq5307
  have eq7874 : ∀ X0 : G, (σ x) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq7873 X0
       have i₂ := eq4478 X0
       grind)
    | exact superpose eq4478 eq7873
    | exact resolve eq7873 eq4478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478 eq7873
  have eq7878 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4865
       have i₂ := eq7874 x
       grind)
    | exact superpose eq7874 eq4865
    | (have r₁ := eq4865
       have r₂ := eq7874 x
       grind)
    | exact resolve eq4865 eq7874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4865 eq7874
  have eq7934 : False := by grind
  exact eq7934

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq59 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq62 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq63 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  clear eq22
  have eq73 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
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
  have eq95 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq110 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq512 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq593 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq61 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq64 X3 X2 X4 X0
       grind)
    | exact superpose eq64 eq61
    | exact resolve eq61 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq64
  have eq772 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq74 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq74 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq13 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq785 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq784 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq787 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq772 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq790 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq787 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq787 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq787 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq868 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq520
    | exact resolve eq520 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq62 eq520
    | exact resolve eq520 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63 eq520
    | exact resolve eq520 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op x X0)
       have i₂ := eq868 x X0
       grind)
    | exact superpose eq868 eq62
    | exact resolve eq62 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq972 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (M.op sF2 x)
       have i₂ := eq868 sF2 x
       grind)
    | exact superpose eq868 eq63
    | exact resolve eq63 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1803 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq790 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq790
    | (have j0 := eq790 (τ X0) X1
       grind)
    | exact resolve eq790 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1811 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1803 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1803
    | (have j0 := eq1803 X0 X1
       grind)
    | exact resolve eq1803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq1817 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1811 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1811
    | (have j0 := eq1811 X0 X1
       grind)
    | exact resolve eq1811 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq3516 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq785 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq785
    | (have j0 := eq785 (τ X0)
       grind)
    | exact resolve eq785 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq785
  have eq3524 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3516 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3516
    | (have j0 := eq3516 X0
       grind)
    | exact resolve eq3516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3516
  have eq3530 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3524 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3524
    | (have j0 := eq3524 X0
       grind)
    | exact resolve eq3524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524
  have eq11939 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq593 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq14 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq14 eq593
    | exact resolve eq593 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq11979 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq11939 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq11939
    | exact resolve eq11939 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11939
  have eq26351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq26351
    | exact resolve eq26351 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26351
  have eq26372 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq26361
       have r₂ := eq27
       grind)
    | exact resolve eq26361 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26361
  have eq26374 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26372 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26372
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq26372
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq26372
       grind)
    | exact resolve eq12 eq26372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26372
  have eq26427 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq26374
  have eq26428 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq26427
  have eq26454 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq26428
       have r₂ := eq13 x (σ x)
       grind)
    | (have r₁ := eq26428
       have r₂ := eq13 x x
       grind)
    | exact resolve eq26428 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26428
  have eq26466 : (τ (σ y)) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26454 eq95
    | exact resolve eq95 eq26454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq26467 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26454 eq97
    | exact resolve eq97 eq26454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq26454
  have eq26484 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq26467
  have eq26492 : y = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq26466
    | exact resolve eq26466 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26466
  have eq26496 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq26492
       have r₂ := eq13 x x
       grind)
    | exact resolve eq26492 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26492
  have eq26498 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq26496
       grind)
    | exact superpose eq26496 eq71
    | exact resolve eq71 eq26496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq26496
  have eq26537 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq26498
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26498
    | exact resolve eq26498 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26498
  have eq26893 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26537 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26537
  have eq26905 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq26893
    | exact resolve eq26893 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26893
  have eq26917 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq26484
       grind)
    | exact superpose eq26484 eq14
    | exact resolve eq14 eq26484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26963 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq868 y x
       have i₂ := eq26484
       grind)
    | exact superpose eq26484 eq868
    | exact resolve eq868 eq26484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26484
  have eq26995 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq26917 X0
       have i₂ := eq868 y X0
       grind)
    | exact superpose eq868 eq26917
    | exact resolve eq26917 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26917
  have eq72865 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26995 y
       have i₂ := eq26963
       grind)
    | exact superpose eq26963 eq26995
    | exact resolve eq26995 eq26963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26963
  have eq72969 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72865
  have eq73375 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26995 x
       have i₂ := eq72969
       grind)
    | exact superpose eq72969 eq26995
    | exact resolve eq26995 eq72969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26995 eq72969
  have eq73437 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq73375
  have eq73444 : y = (M.op (M.op (M.op x y) x) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq73437
       grind)
    | exact superpose eq73437 eq59
    | exact resolve eq59 eq73437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq73465 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq970 x
       have i₂ := eq73437
       grind)
    | exact superpose eq73437 eq970
    | exact resolve eq970 eq73437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq73437
  have eq73551 : x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq870 eq73465
    | exact resolve eq73465 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq73465
  have eq80095 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq73551 eq73444
    | exact resolve eq73444 eq73551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73444 eq73551
  have eq80153 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq80095
  have eq80157 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq80153
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80153
    | exact resolve eq80153 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq80153
  have eq80165 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq80157 eq29
    | exact resolve eq29 eq80157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80157
  have eq80404 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq80165
    | exact resolve eq80165 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq80165
  have eq80405 : y = (M.op x y) := by grind
  clear eq80404
  have eq80789 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq80405 eq20
    | exact resolve eq20 eq80405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq81047 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq80789
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq80789
    | exact resolve eq80789 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80789
  have eq81048 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq81047 eq26
    | exact resolve eq26 eq81047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq81055 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq81047 eq60
    | exact resolve eq60 eq81047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq259657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq81047 eq26905
    | exact resolve eq26905 eq81047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26905
  have eq259658 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq259657
       have r₂ := eq27
       grind)
    | exact resolve eq259657 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259657
  have eq259659 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq81047 eq259658
    | exact resolve eq259658 eq81047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259658
  have eq259747 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq259659 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq259659
       grind)
    | exact resolve eq13 eq259659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259659
  have eq259845 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq259747 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259747
  have eq260001 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq868 X0 x
       have i₂ := eq259845 (M.op X0 x)
       grind)
    | exact superpose eq259845 eq868
    | (have j1 := eq259845 X0
       grind)
    | exact resolve eq868 eq259845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259845
  have eq260161 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (k X1 (σ x)) = X1 ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq260001 (M.op X1 X1)
       grind)
    | exact superpose eq260001 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       have j1 := eq260001 X1
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq260001 X0
       grind)
    | exact resolve eq13 eq260001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260001
  have eq260259 : ∀ X0 X1 : G, y = (M.op y x) ∨ (k X1 (σ x)) = X1 ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq260161 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260161
  have eq260439 : ∀ X0 X1 : G, y = (M.op y y) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq868 y x
       have i₂ := eq260259 X0 X1
       grind)
    | exact superpose eq260259 eq868
    | (have j1 := eq260259 X1 X0
       grind)
    | exact resolve eq868 eq260259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260259
  have eq260527 : ∀ X0 X1 X2 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (k X1 (σ x)) = X1 ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq260439 X1 X2
       grind)
    | exact superpose eq260439 eq13
    | (have j0 := eq13 X0 y
       have j1 := eq260439 X1 X2
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq260439 X0 X1
       grind)
    | exact resolve eq13 eq260439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260439
  have eq260625 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op x y))) = X2 ∨ (k X1 (σ x)) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq260527 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260527
  have eq261049 : ∀ X0 X1 : G, (τ (σ y)) = (k y (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq110
       have i₂ := eq260625 X0 (k sF3 sF1) x
       grind)
    | (have i₁ := eq110
       have i₂ := eq260625 (k sF3 sF1) X1 x
       grind)
    | exact superpose eq260625 eq110
    | (have j1 := eq260625 X1 X0 x
       grind)
    | exact resolve eq110 eq260625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq260625
  have eq261405 : ∀ X0 X1 : G, (τ (σ y)) = (k y y) ∨ (k X0 (σ x)) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | exact superpose eq80405 eq261049
    | (have j0 := eq261049 X0 X1
       grind)
    | exact resolve eq261049 eq80405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80405 eq261049
  have eq261614 : ∀ X0 X1 : G, y = (k y y) ∨ (k X0 (σ x)) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29 eq261405
    | (have j0 := eq261405 X0 y
       grind)
    | exact resolve eq261405 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq261405
  have eq261744 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 (σ x)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq261614 X0 X1
       have j1 := eq1817 y X1
       grind)
    | (have r₁ := eq261614 X0 X1
       have r₂ := eq1817 y X1
       grind)
    | (have r₁ := eq261614 (σ x) X1
       have r₂ := eq1817 (σ x) X1
       grind)
    | (have r₁ := eq261614 X0 y
       have r₂ := eq1817 y X1
       grind)
    | exact resolve eq261614 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817 eq261614
  have eq261982 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq790 y X0
       have i₂ := eq261744 X1 y
       grind)
    | exact superpose eq261744 eq790
    | (have j0 := eq790 y X0
       have j1 := eq261744 X1 X1
       grind)
    | exact resolve eq790 eq261744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq261744
  have eq262170 : ∀ X0 X1 : G, (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq261982 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261982
  have eq262323 : ∀ X0 X1 : G, (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq262170 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq262170
    | (have j0 := eq262170 X0 X1
       grind)
    | exact resolve eq262170 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq262170
  have eq262555 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq81047 eq262323
    | (have j0 := eq262323 X0 X1
       grind)
    | exact resolve eq262323 eq81047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81047 eq262323
  have eq263227 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3530 X0
       have i₂ := eq262555 (k X0 X0) x
       grind)
    | exact superpose eq262555 eq3530
    | (have j0 := eq3530 (σ x)
       have j1 := eq262555 X0 x
       grind)
    | (have r₁ := eq3530 (σ x)
       have r₂ := eq262555 X0 (σ x)
       grind)
    | (have r₁ := eq3530 (σ (M.op x y))
       have r₂ := eq262555 (σ (M.op x y)) x
       grind)
    | exact resolve eq3530 eq262555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262555
  have eq263397 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq263227 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263227
  have eq264093 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq972 X0
       have i₂ := eq263397 (M.op sF2 X0)
       grind)
    | exact superpose eq263397 eq972
    | (have j1 := eq263397 X0
       grind)
    | exact resolve eq972 eq263397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq264118 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq81055 X0
       have i₂ := eq263397 (M.op sF2 X0)
       grind)
    | exact superpose eq263397 eq81055
    | (have j1 := eq263397 X0
       grind)
    | exact resolve eq81055 eq263397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81055 eq263397
  have eq264313 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq872 eq264093
    | (have j0 := eq264093 X0
       grind)
    | exact resolve eq264093 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq264093
  have eq282900 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264118 X0
       have i₂ := eq264313 (M.op sF4 sF2)
       grind)
    | exact superpose eq264313 eq264118
    | (have j0 := eq264118 X0
       have j1 := eq264313 X0
       grind)
    | exact resolve eq264118 eq264313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264118 eq264313
  have eq282983 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq81048 eq282900
    | (have j0 := eq282900 X0 X0
       grind)
    | exact resolve eq282900 eq81048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282900
  have eq282986 : ∀ X0 X1 : G, (k X1 (σ (M.op x y))) = X1 ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq282983 X1 X1
       grind)
    | (have r₁ := eq282983 X0 X1
       have r₂ := eq27
       grind)
    | exact resolve eq282983 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282983
  have eq283310 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq282986 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282986
  have eq283311 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq283310 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283310
  have eq284092 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq283311 eq3530
    | (have j0 := eq3530 (σ (M.op x y))
       grind)
    | (have r₁ := eq3530 (σ (M.op x y))
       have r₂ := eq283311 (σ (M.op x y))
       grind)
    | exact resolve eq3530 eq283311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530 eq283311
  have eq284273 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq284092
  have eq285879 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq284273 eq520
    | exact resolve eq520 eq284273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq285968 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq284273 eq11979
    | exact resolve eq11979 eq284273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11979 eq284273
  have eq285976 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq285968 x
       have i₂ := eq868 sF1 x
       grind)
    | exact superpose eq868 eq285968
    | exact resolve eq285968 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868 eq285968
  have eq300551 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq285976 eq285879
    | exact resolve eq285879 eq285976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285879
  have eq302532 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq300551 eq285976
    | exact resolve eq285976 eq300551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285976 eq300551
  have eq304806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq302532 eq81048
    | exact resolve eq81048 eq302532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81048 eq302532
  have eq304990 : False := by grind
  exact eq304990

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq59 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq62 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq63 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
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
  clear eq71
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq246 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq378 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq14
    | exact resolve eq14 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq457 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq61 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq64 X3 X2 X4 X0
       grind)
    | exact superpose eq64 eq61
    | exact resolve eq61 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq64
  have eq515 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq246
    | exact resolve eq246 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq694 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq74 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq74 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq13 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq705 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq704 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq707 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq694 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq710 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq707 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq707 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq707 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq868 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq386
    | exact resolve eq386 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq62 eq386
    | exact resolve eq386 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63 eq386
    | exact resolve eq386 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op x X0)
       have i₂ := eq868 x X0
       grind)
    | exact superpose eq868 eq62
    | exact resolve eq62 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq972 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (M.op sF2 x)
       have i₂ := eq868 sF2 x
       grind)
    | exact superpose eq868 eq63
    | exact resolve eq63 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1803 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq710 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq710
    | (have j0 := eq710 (τ X0) X1
       grind)
    | exact resolve eq710 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1811 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1803 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1803
    | (have j0 := eq1803 X0 X1
       grind)
    | exact resolve eq1803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq1817 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1811 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1811
    | (have j0 := eq1811 X0 X1
       grind)
    | exact resolve eq1811 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq1871 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1817 (τ X0) X1
       have i₂ := eq515 X0 X0
       grind)
    | exact superpose eq515 eq1817
    | (have j0 := eq1817 (τ X0) X1
       grind)
    | exact resolve eq1817 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515 eq1817
  have eq3516 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
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
  have eq3524 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3516 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3516
    | (have j0 := eq3516 X0
       grind)
    | exact resolve eq3516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3516
  have eq3530 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3524 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3524
    | (have j0 := eq3524 X0
       grind)
    | exact resolve eq3524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524
  have eq10838 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq457 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq14 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq14 eq457
    | exact resolve eq457 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq10878 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq10838 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq10838
    | exact resolve eq10838 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10838
  have eq26448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq26458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq26448
    | exact resolve eq26448 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26448
  have eq26469 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq26458
       have r₂ := eq27
       grind)
    | exact resolve eq26458 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26458
  have eq26518 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26469 eq868
    | exact resolve eq868 eq26469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26469
  have eq26561 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26518 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq26518
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq26518
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq26518
       grind)
    | exact resolve eq13 eq26518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26518
  have eq26608 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq26561 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26561
  have eq26770 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq26608 (M.op X1 X1)
       grind)
    | exact superpose eq26608 eq13
    | (have j0 := eq13 X0 (σ x)
       have j1 := eq26608 X1
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq26608 X0
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq26608 X0
       grind)
    | exact resolve eq13 eq26608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26608
  have eq26817 : ∀ X0 X1 : G, y = (M.op y x) ∨ (k X1 (σ y)) = X1 ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq26770 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26770
  have eq26901 : ∀ X0 X1 : G, y = (M.op y y) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq868 y x
       have i₂ := eq26817 X0 X1
       grind)
    | exact superpose eq26817 eq868
    | (have j1 := eq26817 X1 X0
       grind)
    | exact resolve eq868 eq26817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26817
  have eq27052 : ∀ X0 X1 X2 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (k X1 (σ y)) = X1 ∨ (k X2 (σ x)) = X2 ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq26901 X1 X2
       grind)
    | exact superpose eq26901 eq13
    | (have j0 := eq13 X0 y
       have j1 := eq26901 X1 X2
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq26901 X0 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq26901 X0 X1
       grind)
    | exact resolve eq13 eq26901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26901
  have eq27099 : ∀ X0 X1 X2 : G, x = (M.op x x) ∨ (k X1 (σ y)) = X1 ∨ (k X2 (σ x)) = X2 ∨ (k X0 y) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq27052 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27052
  have eq27264 : ∀ X0 X1 X2 X3 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ y)) = X1 ∨ (k X2 (σ x)) = X2 ∨ (k X3 y) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq27099 X3 X1 X2
       grind)
    | exact superpose eq27099 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq27099 X3 X1 X2
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq27099 X0 X1 X2
       grind)
    | exact resolve eq13 eq27099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27099
  have eq27311 : ∀ X0 X1 X2 X3 : G, (k X3 y) = X3 ∨ (k X1 (σ y)) = X1 ∨ (k X2 (σ x)) = X2 ∨ (k X0 x) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq27264 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27264
  have eq27393 : ∀ X0 X1 X2 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 ∨ (k X2 x) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq705 y
       have i₂ := eq27311 X2 X0 X1 y
       grind)
    | exact superpose eq27311 eq705
    | (have j0 := eq705 y
       have j1 := eq27311 X2 X0 X1 x
       grind)
    | exact resolve eq705 eq27311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27311
  have eq27426 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 ∨ (k X2 x) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq27393 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27393
  have eq27457 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 ∨ (k X2 x) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27426 X0 X1 X2
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27426
    | (have j0 := eq27426 X0 X1 X2
       grind)
    | exact resolve eq27426 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27426
  have eq27518 : ∀ X0 X1 X2 : G, (k X2 x) = X2 ∨ (k X1 (σ x)) = X1 ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq27457 X0 X1 X2
       have j1 := eq13 X2 x
       grind)
    | (have r₁ := eq27457 X0 X1 X2
       have r₂ := eq13 X0 (σ y)
       grind)
    | exact resolve eq27457 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27457
  have eq27649 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq705 x
       have i₂ := eq27518 X1 X0 x
       grind)
    | exact superpose eq27518 eq705
    | (have j0 := eq705 x
       have j1 := eq27518 X1 X0 x
       grind)
    | exact resolve eq705 eq27518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27518
  have eq27682 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27649
  have eq27713 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27682 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27682
    | (have j0 := eq27682 X0 X1
       grind)
    | exact resolve eq27682 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq27682
  have eq27774 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (k X0 (σ x)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27713 X0 X1
       have j1 := eq13 X1 (σ y)
       grind)
    | (have r₁ := eq27713 X0 X1
       have r₂ := eq13 X0 (σ x)
       grind)
    | exact resolve eq27713 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27713
  have eq27844 : ∀ X0 X1 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1871 X0 X1
       have i₂ := eq27774 (k X0 X0) X1
       grind)
    | exact superpose eq27774 eq1871
    | (have j0 := eq1871 (σ y) X0
       have j1 := eq27774 X1 X1
       grind)
    | exact resolve eq1871 eq27774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27774
  have eq27881 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27844 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27844
  have eq27904 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq29 eq27881
    | (have j0 := eq27881 X0 X1
       grind)
    | exact resolve eq27881 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27881
  have eq28261 : ∀ X0 X1 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1871 X0 X1
       have i₂ := eq27904 (k X0 X0) X1
       grind)
    | exact superpose eq27904 eq1871
    | (have j0 := eq1871 (σ x) X0
       have j1 := eq27904 X1 X1
       grind)
    | exact resolve eq1871 eq27904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28262 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq3530 X0
       have i₂ := eq27904 (k X0 X0) x
       grind)
    | exact superpose eq27904 eq3530
    | (have j0 := eq3530 (σ x)
       have j1 := eq27904 X0 x
       grind)
    | (have r₁ := eq3530 (σ x)
       have r₂ := eq27904 X0 (σ x)
       grind)
    | (have r₁ := eq3530 y
       have r₂ := eq27904 y x
       grind)
    | exact resolve eq3530 eq27904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27904
  have eq28297 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq28262 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28262
  have eq28298 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28261
  have eq28321 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | exact superpose eq28 eq28298
    | (have j0 := eq28298 X0 X1
       grind)
    | exact resolve eq28298 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq28298
  have eq28514 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq28297 (M.op sF2 X0)
       grind)
    | exact superpose eq28297 eq60
    | (have j1 := eq28297 X0
       grind)
    | exact resolve eq60 eq28297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq28535 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq972 X0
       have i₂ := eq28297 (M.op sF2 X0)
       grind)
    | exact superpose eq28297 eq972
    | (have j1 := eq28297 X0
       grind)
    | exact resolve eq972 eq28297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq28297
  have eq28612 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq872 eq28535
    | (have j0 := eq28535 X0
       grind)
    | exact resolve eq28535 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq28535
  have eq28735 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq710 y X0
       have i₂ := eq28321 X1 y
       grind)
    | exact superpose eq28321 eq710
    | (have j0 := eq710 y X0
       have j1 := eq28321 X1 X1
       grind)
    | exact resolve eq710 eq28321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq28321
  have eq28764 : ∀ X0 X1 : G, (k X0 (σ y)) = X0 ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28735 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28735
  have eq28796 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28764 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28764
    | (have j0 := eq28764 X0 X1
       grind)
    | exact resolve eq28764 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28764
  have eq29297 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3530 x
       have i₂ := eq28796 X0 x
       grind)
    | exact superpose eq28796 eq3530
    | (have j0 := eq3530 x
       have j1 := eq28796 X0 x
       grind)
    | (have r₁ := eq3530 x
       have r₂ := eq28796 X0 x
       grind)
    | (have r₁ := eq3530 (σ y)
       have r₂ := eq28796 (σ y) x
       grind)
    | exact resolve eq3530 eq28796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28796
  have eq29332 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq29297 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29297
  have eq30134 : ∀ X0 : G, y = (M.op (M.op (M.op x y) x) y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 x
       have i₂ := eq29332 X0
       grind)
    | exact superpose eq29332 eq59
    | (have j1 := eq29332 X0
       grind)
    | exact resolve eq59 eq29332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq30155 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) x) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq970 x
       have i₂ := eq29332 X0
       grind)
    | exact superpose eq29332 eq970
    | (have j1 := eq29332 X0
       grind)
    | exact resolve eq970 eq29332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq29332
  have eq30233 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq870 eq30155
    | (have j0 := eq30155 X0
       grind)
    | exact resolve eq30155 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq30155
  have eq33696 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28514 X0
       have i₂ := eq28612 (M.op sF4 sF2)
       grind)
    | exact superpose eq28612 eq28514
    | (have j0 := eq28514 X0
       have j1 := eq28612 X0
       grind)
    | exact resolve eq28514 eq28612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28514 eq28612
  have eq33749 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq33696
    | (have j0 := eq33696 X1 X1
       grind)
    | exact resolve eq33696 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33696
  have eq35980 : ∀ X0 X1 : G, y = (M.op x y) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30134 X0
       have i₂ := eq30233 (M.op sF0 x)
       grind)
    | exact superpose eq30233 eq30134
    | (have j0 := eq30134 X0
       have j1 := eq30233 X0
       grind)
    | exact resolve eq30134 eq30233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30134 eq30233
  have eq36033 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq35980 X1 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35980
    | (have j0 := eq35980 X1 X1
       grind)
    | exact resolve eq35980 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35980
  have eq40899 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq33749 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33749
  have eq40900 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq40899 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40899
  have eq41069 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq705 y
       have i₂ := eq40900 y
       grind)
    | exact superpose eq40900 eq705
    | (have j0 := eq705 y
       grind)
    | exact resolve eq705 eq40900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq40900
  have eq41104 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq41069
  have eq41138 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41104
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41104
    | exact resolve eq41104 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41104
  have eq41485 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq41138 eq386
    | exact resolve eq386 eq41138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41536 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq41138 eq10878
    | exact resolve eq10878 eq41138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41138
  have eq41539 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41536 x
       have i₂ := eq868 sF3 x
       grind)
    | exact superpose eq868 eq41536
    | exact resolve eq41536 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41536
  have eq68930 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq41539 eq41485
    | exact resolve eq41485 eq41539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41485
  have eq69033 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq68930 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68930
  have eq69463 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq69033 eq41539
    | exact resolve eq41539 eq69033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41539 eq69033
  have eq69604 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq69463 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69463
  have eq70339 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69604 eq26
    | (have j1 := eq69604 (σ x)
       grind)
    | exact resolve eq26 eq69604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq69604
  have eq70379 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq70339
  have eq70739 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq70379 eq27
    | exact resolve eq27 eq70379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq70379
  have eq95404 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36033 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36033
  have eq95405 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq95404 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95404
  have eq96015 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq95405 eq1871
    | (have j0 := eq1871 (σ y) X0
       grind)
    | exact resolve eq1871 eq95405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871 eq95405
  have eq96102 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq96015 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96015
  have eq96186 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq96102
    | exact resolve eq96102 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq96102
  have eq97480 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3530 y
       have i₂ := eq96186 y
       grind)
    | exact superpose eq96186 eq3530
    | (have j0 := eq3530 y
       grind)
    | (have r₁ := eq3530 y
       have r₂ := eq96186 y
       grind)
    | exact resolve eq3530 eq96186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530 eq96186
  have eq97565 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq97480
  have eq98217 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq386 y X0
       have i₂ := eq97565
       grind)
    | exact superpose eq97565 eq386
    | exact resolve eq386 eq97565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq98272 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10878 y y x
       have i₂ := eq97565
       grind)
    | exact superpose eq97565 eq10878
    | exact resolve eq10878 eq97565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10878 eq97565
  have eq98275 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq98272 X0
       have i₂ := eq868 y X0
       grind)
    | exact superpose eq868 eq98272
    | exact resolve eq98272 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868 eq98272
  have eq147613 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq98217 X0
       have i₂ := eq98275 X0
       grind)
    | exact superpose eq98275 eq98217
    | exact resolve eq98217 eq98275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98217
  have eq147719 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq147613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147613
  have eq148558 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq98275 X0
       have i₂ := eq147719 X0
       grind)
    | exact superpose eq147719 eq98275
    | exact resolve eq98275 eq147719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98275 eq147719
  have eq148701 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq148558 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148558
  have eq149069 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq148701 x
       grind)
    | exact superpose eq148701 eq18
    | (have j1 := eq148701 x
       grind)
    | exact resolve eq18 eq148701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq148701
  have eq149153 : y = (M.op x y) := by grind
  clear eq149069
  have eq149179 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq149153 eq20
    | exact resolve eq20 eq149153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq149153
  have eq149516 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq149179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq149179
    | exact resolve eq149179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq149179
  have eq149517 : False := by grind
  exact eq149517

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_y_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq61
    | exact resolve eq61 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq338 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq197 x y
       grind)
    | exact superpose eq197 eq16
    | (have j1 := eq197 x y
       grind)
    | exact resolve eq16 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq197 X0 X0
       grind)
    | exact superpose eq197 eq67
    | (have j1 := eq197 X0 X0
       grind)
    | exact resolve eq67 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq344 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq197 X0 X1
       grind)
    | exact superpose eq197 eq9
    | (have j1 := eq197 X0 X1
       grind)
    | exact resolve eq9 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq197 X0 X1
       grind)
    | exact superpose eq197 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq197 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq197 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq197 X0 X1
       grind)
    | exact resolve eq13 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq197 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq356 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq358 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq345 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq360 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq363 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq358 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq358 X0 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq358 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq358 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq367 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq363 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq363
    | (have j0 := eq363 X0 X1
       grind)
    | exact resolve eq363 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq511 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1413 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq197 (k X0 X0) X0
       have i₂ := eq360 X0
       grind)
    | exact superpose eq360 eq197
    | (have j0 := eq197 X0 X0
       have j1 := eq360 X0
       grind)
    | exact resolve eq197 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq360
  have eq1445 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1413 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1448 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1445 X0
       have j1 := eq357 X0
       grind)
    | (have r₁ := eq1445 X0
       have r₂ := eq357 X0
       grind)
    | exact resolve eq1445 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq1445
  have eq1581 : ∀ X0 : G, (σ (τ X0)) = (σ (k (τ (k X0 X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1448 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq1448
    | (have j0 := eq1448 (τ X0)
       grind)
    | exact resolve eq1448 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1627 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1581 X0
       have i₂ := eq17 (k X0 X0) (τ X0)
       grind)
    | exact superpose eq17 eq1581
    | (have j0 := eq1581 X0
       grind)
    | exact resolve eq1581 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1581
  have eq1633 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 X0) (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq1627 X0
       have j1 := eq12 (k X0 X0) (σ (τ X0))
       grind)
    | (have r₁ := eq1627 X0
       have r₂ := eq12 X0 (σ (τ X0))
       grind)
    | exact resolve eq1627 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq1638 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1633 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1633
    | exact resolve eq1633 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq1643 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1638 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq1638
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq1638 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq1662 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1643 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1679 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1662 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq1662 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1662 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662
  have eq1695 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq1679 (σ X0)
       grind)
    | exact superpose eq1679 eq22
    | exact resolve eq22 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1703 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1695 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1695
    | exact resolve eq1695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq9241 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq338
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq338
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq338 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq9244 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq9241
  have eq11047 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq367 (M.op X0 X0) X0
       have i₂ := eq1679 X0
       grind)
    | exact superpose eq1679 eq367
    | (have j0 := eq367 X0 X0
       grind)
    | exact resolve eq367 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679
  have eq11055 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq367 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq367
    | (have j0 := eq367 X0 (τ X1)
       grind)
    | exact resolve eq367 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq11085 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq11047 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11047
  have eq11100 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11055 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11055
    | (have j0 := eq11055 X0 X1
       grind)
    | exact resolve eq11055 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11055
  have eq11110 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11100 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11100
    | (have j0 := eq11100 X0 X1
       grind)
    | exact resolve eq11100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11100
  have eq11119 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11110 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11110
    | (have j0 := eq11110 X0 X1
       grind)
    | exact resolve eq11110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11110
  have eq11124 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11119 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11119
    | (have j0 := eq11119 X0 X1
       grind)
    | exact resolve eq11119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11119
  have eq11129 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11124 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11124
    | (have j0 := eq11124 X0 X1
       grind)
    | exact resolve eq11124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11124
  have eq11152 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11129 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq1703 X0
       grind)
    | exact superpose eq1703 eq11129
    | (have j0 := eq11129 X0 X0
       grind)
    | exact resolve eq11129 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11129
  have eq11165 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11152 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11152
  have eq11172 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq11165 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11165
    | (have j0 := eq11165 (τ X0)
       grind)
    | exact resolve eq11165 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11165
  have eq11230 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X0)) X2) (σ (τ (k X0 X1)))) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq344 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq344
    | (have j0 := eq344 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq344 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq344
  have eq11383 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X0)) X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11230 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11230
    | (have j0 := eq11230 X0 X1 X2
       grind)
    | exact resolve eq11230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11230
  have eq11399 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11383 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11383
    | (have j0 := eq11383 X0 X1 X2
       grind)
    | exact resolve eq11383 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11383
  have eq11408 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11399 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11399
    | (have j0 := eq11399 X0 X1 X2
       grind)
    | exact resolve eq11399 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11399
  have eq11417 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11408 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11408
    | (have j0 := eq11408 X0 X1 X2
       grind)
    | exact resolve eq11408 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11408
  have eq11422 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11417 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11417
    | (have j0 := eq11417 X0 X1 X2
       grind)
    | exact resolve eq11417 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11417
  have eq12113 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (k X0 X1)
       have i₂ := eq11422 X0 X1 X0
       grind)
    | exact superpose eq11422 eq73
    | (have j1 := eq11422 X0 X1 x
       grind)
    | exact resolve eq73 eq11422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11422
  have eq25751 : y = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1703 y
       have i₂ := eq9244
       grind)
    | exact superpose eq9244 eq1703
    | exact resolve eq1703 eq9244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703 eq9244
  have eq25953 : y = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq12 (τ (σ y)) y
       grind)
    | (have r₁ := eq25751
       have r₂ := eq12 x y
       grind)
    | exact resolve eq25751 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25751
  have eq25966 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25953
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq25953
    | exact resolve eq25953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25953
  have eq25999 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86 (σ x) (σ y)
       have i₂ := eq25966
       grind)
    | exact superpose eq25966 eq86
    | exact resolve eq86 eq25966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25966
  have eq26336 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11172 (σ x)
       have i₂ := eq25999
       grind)
    | exact superpose eq25999 eq11172
    | (have j0 := eq11172 (σ x)
       grind)
    | exact resolve eq11172 eq25999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11172 eq25999
  have eq26434 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq26336
  have eq26469 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26434
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26434
    | exact resolve eq26434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26434
  have eq26550 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12113 y y
       have i₂ := eq26469
       grind)
    | exact superpose eq26469 eq12113
    | (have j0 := eq12113 y y
       grind)
    | exact resolve eq12113 eq26469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12113 eq26469
  have eq26559 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq26550
  have eq26733 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq26559
       grind)
    | exact superpose eq26559 eq73
    | exact resolve eq73 eq26559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26819 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq511 y y x
       have i₂ := eq26559
       grind)
    | exact superpose eq26559 eq511
    | exact resolve eq511 eq26559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26559
  have eq26884 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26819 X0
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq26819
    | exact resolve eq26819 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26819
  have eq43221 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26733 X0
       have i₂ := eq26884 X0
       grind)
    | exact superpose eq26884 eq26733
    | exact resolve eq26733 eq26884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26733 eq26884
  have eq43445 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq43221 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43221
  have eq43495 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq86 x y
       have i₂ := eq43445 X0
       grind)
    | exact superpose eq43445 eq86
    | (have j1 := eq43445 X0
       grind)
    | exact resolve eq86 eq43445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43445
  have eq43611 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq43495 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43495
  have eq43679 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq43611 X1
       grind)
    | exact superpose eq43611 eq73
    | (have j1 := eq43611 X1
       grind)
    | exact resolve eq73 eq43611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43717 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11085 x
       have i₂ := eq43611 X0
       grind)
    | exact superpose eq43611 eq11085
    | (have j0 := eq11085 x
       have j1 := eq43611 X0
       grind)
    | exact resolve eq11085 eq43611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43766 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq511 x x x
       have i₂ := eq43611 X0
       grind)
    | exact superpose eq43611 eq511
    | (have j1 := eq43611 X1
       grind)
    | exact resolve eq511 eq43611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43611
  have eq43849 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq43717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43717
  have eq43879 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43766 X0 X1
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq43766
    | (have j0 := eq43766 X0 X1
       grind)
    | exact resolve eq43766 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43766
  have eq45410 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ x) X0
       have i₂ := eq43849 X1
       grind)
    | exact superpose eq43849 eq73
    | (have j1 := eq43849 X1
       grind)
    | exact resolve eq73 eq43849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq45497 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq511 (σ x) (σ x) x
       have i₂ := eq43849 X0
       grind)
    | exact superpose eq43849 eq511
    | (have j1 := eq43849 X1
       grind)
    | exact resolve eq511 eq43849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43849
  have eq45611 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45497 X0 X1
       have i₂ := eq86 (σ x) X0
       grind)
    | exact superpose eq86 eq45497
    | (have j0 := eq45497 X0 X1
       grind)
    | exact resolve eq45497 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45497
  have eq45838 : ∀ X0 X1 X2 : G, (M.op x X0) = X0 ∨ (M.op y X1) = X1 ∨ (M.op y X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43679 X0 X1
       have i₂ := eq43879 X0 X2
       grind)
    | exact superpose eq43879 eq43679
    | (have j0 := eq43679 X0 X1
       have j1 := eq43879 X0 X1
       grind)
    | exact resolve eq43679 eq43879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43679 eq43879
  have eq46062 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45838 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45838
  have eq46094 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 y X0
       have i₂ := eq46062 y X1
       grind)
    | exact superpose eq46062 eq74
    | (have j1 := eq46062 X0 X1
       grind)
    | exact resolve eq74 eq46062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46442 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46094 X0 X1
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq46094
    | (have j0 := eq46094 X0 X1
       grind)
    | exact resolve eq46094 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq46094
  have eq47279 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46442 X0 X1
       have i₂ := eq46062 X0 X2
       grind)
    | exact superpose eq46062 eq46442
    | (have j0 := eq46442 X0 X1
       have j1 := eq46062 X0 X1
       grind)
    | exact resolve eq46442 eq46062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46062 eq46442
  have eq47564 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq47279 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47279
  have eq48221 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq47564 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47564
  have eq48222 : y = (M.op x y) := by grind
  clear eq48221
  have eq81547 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = X0 ∨ (M.op y X1) = X1 ∨ (M.op y X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45410 X0 X1
       have i₂ := eq45611 X0 X2
       grind)
    | exact superpose eq45611 eq45410
    | (have j0 := eq45410 X0 X1
       have j1 := eq45611 X0 X1
       grind)
    | exact resolve eq45410 eq45611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45410 eq45611
  have eq81843 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq81547 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81547
  have eq81892 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq81843 X0 (σ y)
       grind)
    | exact superpose eq81843 eq16
    | (have j1 := eq81843 X0 x
       grind)
    | exact resolve eq16 eq81843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81843
  have eq82327 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq81892 X0
       have i₂ := eq48222
       grind)
    | exact superpose eq48222 eq81892
    | (have j0 := eq81892 X0
       grind)
    | exact resolve eq81892 eq48222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48222 eq81892
  have eq82328 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82327
  have eq82420 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11085 y
       have i₂ := eq82328 y
       grind)
    | exact superpose eq82328 eq11085
    | (have j0 := eq11085 y
       grind)
    | exact resolve eq11085 eq82328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11085
  have eq82473 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq511 y X1 X0
       have i₂ := eq82328 X0
       grind)
    | exact superpose eq82328 eq511
    | exact resolve eq511 eq82328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq82594 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq74 y X0
       have i₂ := eq82328 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq82328 eq74
    | exact resolve eq74 eq82328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq82779 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq82420
  have eq82889 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq82594 X0
       have i₂ := eq82328 y
       grind)
    | exact superpose eq82328 eq82594
    | exact resolve eq82594 eq82328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82594
  have eq82974 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82473 X0 X0
       have i₂ := eq82328 X0
       grind)
    | exact superpose eq82328 eq82473
    | exact resolve eq82473 eq82328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82473
  have eq83116 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq82889 X0
       have i₂ := eq82328 X0
       grind)
    | exact superpose eq82328 eq82889
    | exact resolve eq82889 eq82328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82328 eq82889
  have eq108594 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq82779
       grind)
    | exact superpose eq82779 eq9
    | exact resolve eq9 eq82779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82779
  have eq108861 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq108594 X0
       have i₂ := eq82974 X0 (σ y)
       grind)
    | exact superpose eq82974 eq108594
    | exact resolve eq108594 eq82974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108594
  have eq109148 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq82974 X0 (σ y)
       have i₂ := eq108861 X0
       grind)
    | exact superpose eq108861 eq82974
    | exact resolve eq82974 eq108861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82974 eq108861
  have eq110581 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109148 (σ x)
       grind)
    | exact superpose eq109148 eq16
    | exact resolve eq16 eq109148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109148
  have eq110699 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq110581
       have i₂ := eq83116 x
       grind)
    | exact superpose eq83116 eq110581
    | exact resolve eq110581 eq83116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83116 eq110581
  have eq110700 : False := by grind
  exact eq110700

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  clear eq43
  have eq59 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq62 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq63 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
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
  have eq74 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq89 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq104 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq106
    | (have j0 := eq106 (σ X0)
       grind)
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq435 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq429 X0
       grind)
    | exact superpose eq429 eq14
    | exact resolve eq14 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq733 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq74 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq74 X0 X0
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq755 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq733 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq756 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq755 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq759 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq756 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq756
    | (have j0 := eq756 X0 X1
       grind)
    | exact resolve eq756 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq822 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq435 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq435
    | exact resolve eq435 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq62 eq435
    | exact resolve eq435 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63 eq435
    | exact resolve eq435 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq912 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op x X0)
       have i₂ := eq822 x X0
       grind)
    | exact superpose eq822 eq62
    | exact resolve eq62 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq914 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (M.op sF2 x)
       have i₂ := eq822 sF2 x
       grind)
    | exact superpose eq822 eq63
    | exact resolve eq63 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq822
  have eq5141 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq340 X0
       grind)
    | exact superpose eq340 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq340 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq340 X0
       grind)
    | exact resolve eq13 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq5153 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5141 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq5141 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq5141 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5141
  have eq12835 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5153 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq5153
    | (have j0 := eq5153 (τ X0) X1
       grind)
    | exact resolve eq5153 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq12842 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12835 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12835
    | (have j0 := eq12835 X0 X1
       grind)
    | exact resolve eq12835 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12835
  have eq12848 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12842 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12842
    | (have j0 := eq12842 X0 X1
       grind)
    | exact resolve eq12842 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12842
  have eq13722 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq759 X0 X1
       have j1 := eq752 X0 X1
       grind)
    | (have r₁ := eq759 X0 X1
       have r₂ := eq752 X0 X1
       grind)
    | (have r₁ := eq759 X1 X1
       have r₂ := eq752 X1 X1
       grind)
    | exact resolve eq759 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq759
  have eq13810 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13722 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13722
    | (have j0 := eq13722 x X0
       grind)
    | exact resolve eq13722 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13722
  have eq18422 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13810 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13810
    | (have j0 := eq13810 y
       grind)
    | exact resolve eq13810 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13810
  have eq18481 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18422
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq18422
    | exact resolve eq18422 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18422
  have eq18498 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq18481
    | exact resolve eq18481 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18481
  have eq18657 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18498 eq89
    | exact resolve eq89 eq18498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq19234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq92 eq18498
    | exact resolve eq18498 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq19239 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq19234
       have r₂ := eq27
       grind)
    | exact resolve eq19234 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19234
  have eq19258 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19239 eq60
    | exact resolve eq60 eq19239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19275 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19239 eq914
    | exact resolve eq914 eq19239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19279 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq19239 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq19239
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq19239
       grind)
    | exact resolve eq13 eq19239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19239
  have eq19315 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq19279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19279
  have eq19332 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq826 eq19275
    | exact resolve eq19275 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19275
  have eq19384 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq104
       have i₂ := eq19315 X0
       grind)
    | (have i₁ := eq104
       have i₂ := eq19315 (M.op x x)
       grind)
    | exact superpose eq19315 eq104
    | (have j1 := eq19315 X0
       grind)
    | (have r₁ := eq104
       have r₂ := eq19315 X0
       grind)
    | exact resolve eq104 eq19315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19444 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq19315 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19315
  have eq19446 : ∀ X0 : G, x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq19384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19384
  have eq19610 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19332 eq19258
    | exact resolve eq19258 eq19332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19258 eq19332
  have eq19646 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq19610
  have eq19647 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq19646
    | exact resolve eq19646 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19646
  have eq19694 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq19647
       grind)
    | exact superpose eq19647 eq104
    | (have r₁ := eq104
       have r₂ := eq19647
       grind)
    | exact resolve eq104 eq19647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq19754 : x ≠ (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq19647
  have eq19756 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq19694
  have eq20321 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq19756
       have r₂ := eq19754
       grind)
    | exact resolve eq19756 eq19754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19754 eq19756
  have eq20324 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq20321
       grind)
    | exact superpose eq20321 eq71
    | exact resolve eq71 eq20321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq20321
  have eq20345 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq20324
    | exact resolve eq20324 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20324
  have eq20405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20345 eq18498
    | exact resolve eq18498 eq20345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18498 eq20345
  have eq20410 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq20405
       have r₂ := eq27
       grind)
    | exact resolve eq20405 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20405
  have eq20447 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq20410 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq20410
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq20410
       grind)
    | exact resolve eq13 eq20410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20410
  have eq20489 : ∀ X0 : G, x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq20447 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20447
  have eq20643 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq20489 X1
       grind)
    | exact superpose eq20489 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq20489 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq20489 X0
       grind)
    | exact resolve eq13 eq20489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20489
  have eq20686 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq20643 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20643
  have eq20840 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq20686 (k sF2 sF2) x
       grind)
    | exact superpose eq20686 eq49
    | (have j1 := eq20686 X0 x
       grind)
    | exact resolve eq49 eq20686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20686
  have eq20935 : ∀ X0 : G, x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq20840
    | (have j0 := eq20840 x
       grind)
    | exact resolve eq20840 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20840
  have eq20972 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq20935 X0
       have j1 := eq12848 x X0
       grind)
    | (have r₁ := eq20935 X0
       have r₂ := eq12848 x x
       grind)
    | (have r₁ := eq20935 x
       have r₂ := eq12848 x x
       grind)
    | exact resolve eq20935 eq12848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20935
  have eq21081 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5153 x X0
       have i₂ := eq20972 x
       grind)
    | exact superpose eq20972 eq5153
    | (have j0 := eq5153 x X0
       grind)
    | exact resolve eq5153 eq20972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5153 eq20972
  have eq21105 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq21081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21081
  have eq21130 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq21105 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21105
    | (have j0 := eq21105 X0
       grind)
    | exact resolve eq21105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21105
  have eq21581 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21130 eq106
    | (have j0 := eq106 (σ x)
       grind)
    | exact resolve eq106 eq21130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21130
  have eq21603 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21581
  have eq21982 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21603 eq60
    | exact resolve eq60 eq21603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq21999 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21603 eq914
    | exact resolve eq914 eq21603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq21603
  have eq22062 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq826 eq21999
    | exact resolve eq21999 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826 eq21999
  have eq24188 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22062 eq21982
    | exact resolve eq21982 eq22062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21982 eq22062
  have eq24227 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24188
  have eq24228 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24227
    | exact resolve eq24227 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq24227
  have eq24229 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24228
  have eq24230 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq24229 eq27
    | exact resolve eq27 eq24229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq81003 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq19446 X0
       have j1 := eq19444 X0
       grind)
    | (have r₁ := eq19446 X0
       have r₂ := eq19444 X0
       grind)
    | exact resolve eq19446 eq19444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19444 eq19446
  have eq81020 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18657
       have i₂ := eq81003 X0
       grind)
    | (have i₁ := eq18657
       have i₂ := eq81003 (k y x)
       grind)
    | exact superpose eq81003 eq18657
    | (have j1 := eq81003 X0
       grind)
    | exact resolve eq18657 eq81003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18657 eq81003
  have eq81031 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq81020 X0
       have j1 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq81020 X0
       have r₂ := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq81020 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq81020 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81020
  have eq81048 : ∀ X0 : G, (M.op x y) = (τ (σ y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq24229 eq81031
    | (have j0 := eq81031 X0
       grind)
    | exact resolve eq81031 eq24229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24229 eq81031
  have eq81051 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq81048
    | (have j0 := eq81048 X0
       grind)
    | exact resolve eq81048 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq81048
  have eq81074 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ x)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq81051 X1
       grind)
    | exact superpose eq81051 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq81051 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq81051 X0
       grind)
    | exact resolve eq13 eq81051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81051
  have eq81124 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq81074 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81074
  have eq81840 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq81124 (k sF2 sF2) x
       grind)
    | exact superpose eq81124 eq49
    | (have j1 := eq81124 X0 x
       grind)
    | exact resolve eq49 eq81124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq81124
  have eq82094 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq81840
    | (have j0 := eq81840 x
       grind)
    | exact resolve eq81840 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq81840
  have eq82212 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq82094 X0
       have j1 := eq12848 x X0
       grind)
    | (have r₁ := eq82094 X0
       have r₂ := eq12848 x x
       grind)
    | (have r₁ := eq82094 x
       have r₂ := eq12848 x x
       grind)
    | exact resolve eq82094 eq12848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12848 eq82094
  have eq82328 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106 x
       have i₂ := eq82212 x
       grind)
    | exact superpose eq82212 eq106
    | (have j0 := eq106 x
       grind)
    | exact resolve eq106 eq82212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq82212
  have eq82439 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq82328
  have eq83334 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq82439
       grind)
    | exact superpose eq82439 eq59
    | exact resolve eq59 eq82439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq83351 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq912 x
       have i₂ := eq82439
       grind)
    | exact superpose eq82439 eq912
    | exact resolve eq912 eq82439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912 eq82439
  have eq83423 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq824 eq83351
    | exact resolve eq83351 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq83351
  have eq89906 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq83423 eq83334
    | exact resolve eq83334 eq83423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83334 eq83423
  have eq89952 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq89906
  have eq89953 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq89952
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89952
    | exact resolve eq89952 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq89952
  have eq89954 : y = (M.op x y) := by grind
  clear eq89953
  have eq90021 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq89954 eq20
    | exact resolve eq20 eq89954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq89954
  have eq90329 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq90021
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq90021
    | exact resolve eq90021 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq90021
  have eq90330 : False := by grind
  exact eq90330

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq17
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54
    | (have j0 := eq54 (σ X0) (σ X1)
       grind)
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq124 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 y x
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq65 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq135 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq133 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq133 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq332 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq124
    | (have j1 := eq54 (σ y) (σ x)
       grind)
    | exact resolve eq124 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq335 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq332
  have eq337 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq335
       grind)
    | exact superpose eq335 eq9
    | exact resolve eq9 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq546 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq135 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq135
    | (have j0 := eq135 (τ X0) X1
       grind)
    | exact resolve eq135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq135
  have eq548 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq551 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq548
    | (have j0 := eq548 X0 X1
       grind)
    | exact resolve eq548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq597 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq551 (τ X0) X1
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq551
    | (have j0 := eq551 (τ X0) X1
       grind)
    | exact resolve eq551 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq551
  have eq2222 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq337 x
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq337
    | exact resolve eq337 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq2344 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq2222
       grind)
    | exact superpose eq2222 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq2222
       grind)
    | exact resolve eq12 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq2380 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2344 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344
  have eq2472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq124
       have i₂ := eq2380 y
       grind)
    | exact superpose eq2380 eq124
    | exact resolve eq124 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq2380
  have eq2473 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2472
  have eq2474 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2473
  have eq2479 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq2474
       grind)
    | exact superpose eq2474 eq9
    | exact resolve eq9 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq2622 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2479 (σ x)
       have i₂ := eq77 (σ x)
       grind)
    | exact superpose eq77 eq2479
    | exact resolve eq2479 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2479
  have eq2759 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq2622
       grind)
    | exact superpose eq2622 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq2622
       grind)
    | exact resolve eq12 eq2622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2799 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq2759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq3154 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2799 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq2799
    | exact resolve eq2799 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3162 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq597 (σ x) X0
       have i₂ := eq2799 (σ x)
       grind)
    | exact superpose eq2799 eq597
    | (have j0 := eq597 (σ x) X0
       grind)
    | exact resolve eq597 eq2799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq2799
  have eq3191 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq3162 X0
       have i₂ := eq2622
       grind)
    | exact superpose eq2622 eq3162
    | (have j0 := eq3162 X0
       grind)
    | exact resolve eq3162 eq2622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2622 eq3162
  have eq3192 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) := by
    intro X0
    first
    | (have j0 := eq3191 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191
  have eq3194 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq3192 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3192
    | exact resolve eq3192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq3441 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq3154 X0
       have i₂ := eq3194 X0
       grind)
    | exact superpose eq3194 eq3154
    | exact resolve eq3154 eq3194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154 eq3194
  have eq3772 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3441 y
       grind)
    | exact superpose eq3441 eq16
    | (have r₁ := eq16
       have r₂ := eq3441 y
       grind)
    | exact resolve eq16 eq3441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3441
  have eq3837 : False := by grind
  exact eq3837
