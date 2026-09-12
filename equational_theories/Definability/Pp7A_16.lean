import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_x_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  clear eq36
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
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
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq65 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq64
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq65
    | exact resolve eq65 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq68
    | exact resolve eq68 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq56
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq75
  have eq244 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y) (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq560 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq50
    | (have j1 := eq61 X0 X0
       grind)
    | exact resolve eq50 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq574 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq560 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq578 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq566 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq566
    | (have j0 := eq566 X0 X1
       grind)
    | exact resolve eq566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq3395 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq420 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq420
    | exact resolve eq420 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq3423 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3395
    | (have j0 := eq3395 (σ y) (σ x)
       grind)
    | exact resolve eq3395 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3742 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq574 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq574
    | (have j0 := eq574 (τ X0)
       grind)
    | exact resolve eq574 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq574
  have eq3763 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3742 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3742
    | (have j0 := eq3742 X0
       grind)
    | exact resolve eq3742 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3742
  have eq3775 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3763 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3763
    | (have j0 := eq3763 X0
       grind)
    | exact resolve eq3763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3763
  have eq4016 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq423 X0 X0 X2 X3 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq423
    | exact resolve eq423 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq20614 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4016 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq4016
    | exact resolve eq4016 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq4016
  have eq26275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq69 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq26276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq26275
    | exact resolve eq26275 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26275
  have eq26287 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26276
       have r₂ := eq28
       grind)
    | exact resolve eq26276 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26276
  have eq26319 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26287 eq3395
    | exact resolve eq3395 eq26287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27937 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26319 eq26287
    | exact resolve eq26287 eq26319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26287 eq26319
  have eq27977 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq27937
  have eq28006 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27977 eq52
    | exact resolve eq52 eq27977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27977
  have eq28025 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq28006
  have eq28086 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28025 eq20614
    | exact resolve eq20614 eq28025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28025
  have eq28090 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28086
    | exact resolve eq28086 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28086
  have eq28134 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3395 x y
       have i₂ := eq28090
       grind)
    | exact superpose eq28090 eq3395
    | exact resolve eq3395 eq28090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3395
  have eq29814 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28090
       have i₂ := eq28134
       grind)
    | exact superpose eq28134 eq28090
    | exact resolve eq28090 eq28134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28090 eq28134
  have eq29856 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq29814
  have eq29887 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq29856
       grind)
    | exact superpose eq29856 eq52
    | exact resolve eq52 eq29856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29856
  have eq29908 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29887
  have eq29939 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq29952 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq29908
       grind)
    | exact superpose eq29908 eq52
    | exact resolve eq52 eq29908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq29971 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20614 y y
       have i₂ := eq29908
       grind)
    | exact superpose eq29908 eq20614
    | exact resolve eq20614 eq29908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20614 eq29908
  have eq29975 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29971
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29971
    | exact resolve eq29971 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29971
  have eq29992 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29975 eq244
    | exact resolve eq244 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq29999 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29975 eq3423
    | exact resolve eq3423 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3423
  have eq30052 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq29999
    | exact resolve eq29999 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29999
  have eq30190 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq29952
       grind)
    | exact superpose eq29952 eq67
    | exact resolve eq67 eq29952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq29952
  have eq30239 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30190
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30190
    | exact resolve eq30190 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30190
  have eq32197 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30052 eq29992
    | exact resolve eq29992 eq30052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29992 eq30052
  have eq32243 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq32197
  have eq32248 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29975 eq32243
    | exact resolve eq32243 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29975 eq32243
  have eq32285 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32248
  have eq32361 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32285 eq77
    | exact resolve eq77 eq32285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq32285
  have eq32413 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq32361
    | exact resolve eq32361 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32361
  have eq35492 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30239 eq56
    | exact resolve eq56 eq30239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35511 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30239 eq3775
    | (have j0 := eq3775 (σ x)
       grind)
    | exact resolve eq3775 eq30239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30239
  have eq35529 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq35511
    | exact resolve eq35511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35511
  have eq35530 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq35529
  have eq35539 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq35492
    | exact resolve eq35492 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35492
  have eq35694 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq35530
  have eq35914 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq35694 eq56
    | exact resolve eq56 eq35694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35694
  have eq35970 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq35914
    | exact resolve eq35914 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35914
  have eq36072 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3775 x
       have i₂ := eq32413
       grind)
    | exact superpose eq32413 eq3775
    | (have j0 := eq3775 x
       grind)
    | exact resolve eq3775 eq32413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775
  have eq36095 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36072
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36072
    | exact resolve eq36072 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36072
  have eq36096 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq36095
  have eq36147 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq35539
       have i₂ := eq35970
       grind)
    | exact superpose eq35970 eq35539
    | exact resolve eq35539 eq35970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35539 eq35970
  have eq36175 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq36147
  have eq36202 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq36175 eq28
    | exact resolve eq28 eq36175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36175
  have eq45100 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq36096
  have eq46119 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32413
       have i₂ := eq45100
       grind)
    | exact superpose eq45100 eq32413
    | exact resolve eq32413 eq45100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32413 eq45100
  have eq46149 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq46119
  have eq46457 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq46149 eq30
    | exact resolve eq30 eq46149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq46149
  have eq46729 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq46457
    | exact resolve eq46457 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46457
  have eq46730 : x = (M.op x y) ∨ x = y := by grind
  clear eq46729
  have eq46731 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq46730 eq21
    | exact resolve eq21 eq46730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46730
  have eq46957 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq46731
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq46731
    | exact resolve eq46731 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46731
  have eq46958 : x = y := by
    first
    | (have r₁ := eq46957
       have r₂ := eq36202
       grind)
    | exact resolve eq46957 eq36202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36202 eq46957
  have eq46959 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq46958
       grind)
    | exact superpose eq46958 eq19
    | exact resolve eq19 eq46958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq46960 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq46958
       grind)
    | exact superpose eq46958 eq25
    | exact resolve eq25 eq46958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq47099 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29939
       have i₂ := eq46958
       grind)
    | exact superpose eq46958 eq29939
    | exact resolve eq29939 eq46958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29939 eq46958
  have eq47198 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq46960
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq46960
    | exact resolve eq46960 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46960
  have eq47203 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq47198 eq27
    | exact resolve eq27 eq47198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq47198
  have eq47611 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq52834 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq578 x x
       have i₂ := eq47099
       grind)
    | exact superpose eq47099 eq578
    | (have j0 := eq578 x x
       grind)
    | exact resolve eq578 eq47099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq47099
  have eq52843 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq52834
  have eq52844 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq52843
  have eq52857 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52844
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52844
    | exact resolve eq52844 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52844
  have eq52880 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47203 eq52857
    | exact resolve eq52857 eq47203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47203 eq52857
  have eq52881 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq52880
  have eq52901 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq52881 eq28
    | exact resolve eq28 eq52881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq52986 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq52881 eq47611
    | exact resolve eq47611 eq52881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47611 eq52881
  have eq53094 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq52986 eq56
    | exact resolve eq56 eq52986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq52986
  have eq53159 : x = (k x x) := by
    first
    | exact superpose eq29 eq53094
    | exact resolve eq53094 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq53094
  have eq53202 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq53159
       grind)
    | exact superpose eq53159 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq53159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53159
  have eq53203 : x = (M.op x x) := by grind
  clear eq53202
  have eq53219 : x = (M.op x y) := by
    first
    | (have i₁ := eq53203
       have i₂ := eq46959
       grind)
    | exact superpose eq46959 eq53203
    | exact resolve eq53203 eq46959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46959 eq53203
  have eq53256 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq53219 eq21
    | exact resolve eq21 eq53219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq53219
  have eq53541 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53256
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53256
    | exact resolve eq53256 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq53256
  have eq53619 : False := by grind
  exact eq53619

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  clear eq36
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
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
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq65 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq64
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq65
    | exact resolve eq65 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq68
    | exact resolve eq68 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq56
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq75
  have eq244 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y) (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq591 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq50
    | (have j1 := eq61 X0 X0
       grind)
    | exact resolve eq50 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq605 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq591 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq609 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq597
    | (have j0 := eq597 X0 X1
       grind)
    | exact resolve eq597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq3349 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq456
    | exact resolve eq456 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq3377 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3349
    | (have j0 := eq3349 (σ y) (σ x)
       grind)
    | exact resolve eq3349 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3806 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq605 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq605
    | (have j0 := eq605 (τ X0)
       grind)
    | exact resolve eq605 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq605
  have eq3828 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3806 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3806
    | (have j0 := eq3806 X0
       grind)
    | exact resolve eq3806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq3841 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3828 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3828
    | (have j0 := eq3828 X0
       grind)
    | exact resolve eq3828 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828
  have eq4070 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq459 X0 X0 X2 X3 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq459
    | exact resolve eq459 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq20922 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4070 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq4070
    | exact resolve eq4070 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq4070
  have eq26527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq69 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq26528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq26527
    | exact resolve eq26527 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26527
  have eq26539 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26528
       have r₂ := eq28
       grind)
    | exact resolve eq26528 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26528
  have eq26571 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26539 eq3349
    | exact resolve eq3349 eq26539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27951 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26571 eq26539
    | exact resolve eq26539 eq26571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26539 eq26571
  have eq27991 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq27951
  have eq28020 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27991 eq52
    | exact resolve eq52 eq27991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27991
  have eq28039 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq28020
  have eq28100 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28039 eq20922
    | exact resolve eq20922 eq28039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28039
  have eq28104 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28100
    | exact resolve eq28100 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28100
  have eq28148 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3349 x y
       have i₂ := eq28104
       grind)
    | exact superpose eq28104 eq3349
    | exact resolve eq3349 eq28104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq30003 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28104
       have i₂ := eq28148
       grind)
    | exact superpose eq28148 eq28104
    | exact resolve eq28104 eq28148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28104 eq28148
  have eq30045 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq30003
  have eq30076 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq30045
       grind)
    | exact superpose eq30045 eq52
    | exact resolve eq52 eq30045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30045
  have eq30097 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30076
  have eq30128 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq30141 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq30097
       grind)
    | exact superpose eq30097 eq52
    | exact resolve eq52 eq30097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq30160 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20922 y y
       have i₂ := eq30097
       grind)
    | exact superpose eq30097 eq20922
    | exact resolve eq20922 eq30097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20922 eq30097
  have eq30164 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30160
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30160
    | exact resolve eq30160 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30160
  have eq30181 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30164 eq244
    | exact resolve eq244 eq30164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq30188 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30164 eq3377
    | exact resolve eq3377 eq30164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377
  have eq30241 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq30188
    | exact resolve eq30188 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30188
  have eq30431 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq30141
       grind)
    | exact superpose eq30141 eq67
    | exact resolve eq67 eq30141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq30141
  have eq30480 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30431
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30431
    | exact resolve eq30431 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30431
  have eq32505 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30241 eq30181
    | exact resolve eq30181 eq30241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30181 eq30241
  have eq32551 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq32505
  have eq32556 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30164 eq32551
    | exact resolve eq32551 eq30164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30164 eq32551
  have eq32593 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32556
  have eq32664 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32593 eq77
    | exact resolve eq77 eq32593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq32593
  have eq32715 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq32664
    | exact resolve eq32664 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32664
  have eq35628 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30480 eq56
    | exact resolve eq56 eq30480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35647 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30480 eq3841
    | (have j0 := eq3841 (σ x)
       grind)
    | exact resolve eq3841 eq30480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30480
  have eq35662 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq35647
    | exact resolve eq35647 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35647
  have eq35663 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq35662
  have eq35672 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq35628
    | exact resolve eq35628 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35628
  have eq35821 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq35663
  have eq36031 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq35821 eq56
    | exact resolve eq56 eq35821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35821
  have eq36084 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq36031
    | exact resolve eq36031 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36031
  have eq36185 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3841 x
       have i₂ := eq32715
       grind)
    | exact superpose eq32715 eq3841
    | (have j0 := eq3841 x
       grind)
    | exact resolve eq3841 eq32715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3841
  have eq36205 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36185
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36185
    | exact resolve eq36185 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36185
  have eq36206 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq36205
  have eq36255 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq35672
       have i₂ := eq36084
       grind)
    | exact superpose eq36084 eq35672
    | exact resolve eq35672 eq36084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35672 eq36084
  have eq36281 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq36255
  have eq36307 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq36281 eq28
    | exact resolve eq28 eq36281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36281
  have eq43632 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq36206
  have eq44615 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32715
       have i₂ := eq43632
       grind)
    | exact superpose eq43632 eq32715
    | exact resolve eq32715 eq43632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32715 eq43632
  have eq44643 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq44615
  have eq44668 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq44643 eq30
    | exact resolve eq30 eq44643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq44643
  have eq44939 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq44668
    | exact resolve eq44668 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44668
  have eq44940 : x = (M.op x y) ∨ x = y := by grind
  clear eq44939
  have eq45215 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq44940 eq21
    | exact resolve eq21 eq44940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44940
  have eq45440 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq45215
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45215
    | exact resolve eq45215 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45215
  have eq45441 : x = y := by
    first
    | (have r₁ := eq45440
       have r₂ := eq36307
       grind)
    | exact resolve eq45440 eq36307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36307 eq45440
  have eq45442 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq45441
       grind)
    | exact superpose eq45441 eq19
    | exact resolve eq19 eq45441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq45443 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq45441
       grind)
    | exact superpose eq45441 eq25
    | exact resolve eq25 eq45441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq45576 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30128
       have i₂ := eq45441
       grind)
    | exact superpose eq45441 eq30128
    | exact resolve eq30128 eq45441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30128 eq45441
  have eq45670 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq45443
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45443
    | exact resolve eq45443 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45443
  have eq45673 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq45670 eq27
    | exact resolve eq27 eq45670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq45670
  have eq46082 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq50289 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq609 x x
       have i₂ := eq45576
       grind)
    | exact superpose eq45576 eq609
    | (have j0 := eq609 x x
       grind)
    | exact resolve eq609 eq45576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq45576
  have eq50298 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50289
  have eq50299 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50298
  have eq50312 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50299
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq50299
    | exact resolve eq50299 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50299
  have eq50334 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45673 eq50312
    | exact resolve eq50312 eq45673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45673 eq50312
  have eq50335 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50334
  have eq50354 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq50335 eq28
    | exact resolve eq28 eq50335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq50439 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq50335 eq46082
    | exact resolve eq46082 eq50335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46082 eq50335
  have eq51157 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq50439 eq56
    | exact resolve eq56 eq50439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq50439
  have eq51219 : x = (k x x) := by
    first
    | exact superpose eq29 eq51157
    | exact resolve eq51157 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq51157
  have eq51261 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq51219
       grind)
    | exact superpose eq51219 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq51219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51219
  have eq51262 : x = (M.op x x) := by grind
  clear eq51261
  have eq51278 : x = (M.op x y) := by
    first
    | (have i₁ := eq51262
       have i₂ := eq45442
       grind)
    | exact superpose eq45442 eq51262
    | exact resolve eq51262 eq45442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45442 eq51262
  have eq51313 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq51278 eq21
    | exact resolve eq21 eq51278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq51278
  have eq51595 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq51313
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq51313
    | exact resolve eq51313 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq51313
  have eq51672 : False := by grind
  exact eq51672

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq68 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
  have eq69 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq68
    | (have j0 := eq68 (σ X0) (σ X1)
       grind)
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq68 x x
       grind)
    | exact superpose eq68 eq44
    | (have j1 := eq68 x x
       grind)
    | exact resolve eq44 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq45
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq45 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq232 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq236 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq235 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq235
    | (have j0 := eq235 X0
       grind)
    | exact resolve eq235 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq271 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq232 eq14
    | exact resolve eq14 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq54
    | (have j1 := eq86 X0 X0
       grind)
    | exact resolve eq54 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq14
    | (have j1 := eq86 X0 X0
       grind)
    | exact resolve eq14 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq433 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0) X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq102 eq68
    | (have j0 := eq68 (σ x) (σ y)
       grind)
    | exact resolve eq68 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq635
    | exact resolve eq635 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq639 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq636
       have r₂ := eq28
       grind)
    | exact resolve eq636 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq689 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq639 eq54
    | exact resolve eq54 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq639 eq56
    | exact resolve eq56 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq695 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq689
    | exact resolve eq689 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq701 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq695
       grind)
    | exact superpose eq695 eq54
    | exact resolve eq54 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq695
       grind)
    | exact superpose eq695 eq56
    | exact resolve eq56 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq701
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq701
    | exact resolve eq701 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq708 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq707 eq271
    | exact resolve eq271 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq707 eq28
    | exact resolve eq28 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 : G, x ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq705
       grind)
    | exact superpose eq705 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq2533 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq447
    | exact resolve eq447 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq3758 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq366 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq366
    | (have j0 := eq366 (τ X0)
       grind)
    | exact resolve eq366 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq3773 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3758 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3758
    | (have j0 := eq3758 X0
       grind)
    | exact resolve eq3758 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3758
  have eq3784 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3773 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3773
    | (have j0 := eq3773 X0
       grind)
    | exact resolve eq3773 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3773
  have eq4512 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op X1 (M.op (σ (τ X0)) X2)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq367 (τ X0) X1 X2
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq367
    | (have j0 := eq367 (τ X0) X1 X2
       grind)
    | exact resolve eq367 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq367
  have eq4528 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4512 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4512
    | (have j0 := eq4512 X0 X1 X2
       grind)
    | exact resolve eq4512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4512
  have eq4539 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4528 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4528
    | (have j0 := eq4528 X0 X1 X2
       grind)
    | exact resolve eq4528 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4528
  have eq5483 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq433 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq56 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq56 eq433
    | exact resolve eq433 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq17150 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq693 eq240
    | exact resolve eq240 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq17382 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17150 eq102
    | exact resolve eq102 eq17150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17383 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17150 eq60
    | exact resolve eq60 eq17150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17150
  have eq17388 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq17382
  have eq17390 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq17383
    | exact resolve eq17383 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17383
  have eq17439 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq17388
       grind)
    | exact superpose eq17388 eq54
    | exact resolve eq54 eq17388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17388
  have eq17457 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17439
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17439
    | exact resolve eq17439 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17439
  have eq17458 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17457 eq27
    | exact resolve eq27 eq17457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17459 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17457 eq30
    | exact resolve eq30 eq17457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17457
  have eq17545 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq17459
    | exact resolve eq17459 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17459
  have eq17550 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17545 eq27
    | exact resolve eq27 eq17545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17551 : y = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17545 eq30
    | exact resolve eq30 eq17545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq17554 : (k x y) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17545 eq60
    | exact resolve eq60 eq17545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17545
  have eq17633 : (k x y) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq64 eq17554
    | exact resolve eq17554 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17554
  have eq17636 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq17551
    | exact resolve eq17551 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17551
  have eq17966 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17458 eq54
    | exact resolve eq54 eq17458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18061 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17550 eq2533
    | exact resolve eq2533 eq17550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18062 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq707 eq17966
    | exact resolve eq17966 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17966
  have eq18089 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq18062
  have eq18739 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq17390
       grind)
    | exact superpose eq17390 eq68
    | (have j0 := eq68 x y
       grind)
    | exact resolve eq68 eq17390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17390
  have eq18740 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq18739
  have eq18742 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18740
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18740
    | exact resolve eq18740 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18740
  have eq18808 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq18742
       grind)
    | exact superpose eq18742 eq54
    | exact resolve eq54 eq18742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18742
  have eq18826 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18808
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18808
    | exact resolve eq18808 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18808
  have eq20720 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq695
       grind)
    | exact superpose eq695 eq92
    | exact resolve eq92 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq695
  have eq20774 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20720
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20720
    | exact resolve eq20720 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20720
  have eq20791 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20774 eq3784
    | (have j0 := eq3784 (σ x)
       grind)
    | exact resolve eq3784 eq20774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3784
  have eq20796 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq20791
    | exact resolve eq20791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20791
  have eq20797 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq20796
  have eq20830 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20797 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq20797
       grind)
    | exact resolve eq13 eq20797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20797
  have eq20849 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20830
  have eq22520 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20849 eq20774
    | exact resolve eq20774 eq20849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20774 eq20849
  have eq22560 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22520
  have eq22701 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22560 eq54
    | exact resolve eq54 eq22560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22560
  have eq22721 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq22701
    | exact resolve eq22701 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22701
  have eq22722 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq22721
  have eq22723 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq22722 eq28
    | exact resolve eq28 eq22722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22727 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22722 eq271
    | exact resolve eq271 eq22722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq22722
  have eq23333 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq27 eq22727
    | (have j0 := eq22727 (σ x)
       grind)
    | exact resolve eq22727 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22727
  have eq24456 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq708 eq238
    | exact resolve eq238 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq708
  have eq25263 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18089 eq24456
    | exact resolve eq24456 eq18089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18089 eq24456
  have eq25316 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq25263
  have eq25322 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq25316
    | exact resolve eq25316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25316
  have eq25326 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25322 eq232
    | exact resolve eq232 eq25322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25322
  have eq25432 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq707 eq25326
    | exact resolve eq25326 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25492 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq25432
  have eq26178 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25492 eq17458
    | exact resolve eq17458 eq25492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17458 eq25492
  have eq26224 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq26178
  have eq42102 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq707 eq18061
    | exact resolve eq18061 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18061
  have eq42120 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq42102
  have eq46036 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq25326 eq236
    | exact resolve eq236 eq25326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25326
  have eq46047 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq46036 X0
       grind)
    | (have r₁ := eq46036 X0
       have r₂ := eq26224
       grind)
    | exact resolve eq46036 eq26224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26224 eq46036
  have eq50231 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq42120 eq17550
    | exact resolve eq17550 eq42120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17550 eq42120
  have eq50252 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq50231
  have eq50270 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq50252 eq240
    | exact resolve eq240 eq50252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50252
  have eq50298 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq50270
       have r₂ := eq28
       grind)
    | exact resolve eq50270 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50270
  have eq50630 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq707 eq50298
    | exact resolve eq50298 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50298
  have eq50637 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq50630
  have eq50830 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq50637 eq64
    | exact resolve eq64 eq50637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50637
  have eq50840 : (M.op x y) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq50830
    | exact resolve eq50830 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50830
  have eq52275 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq50840 eq17633
    | exact resolve eq17633 eq50840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17633 eq50840
  have eq52284 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq52275
  have eq52411 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq52284
       grind)
    | exact superpose eq52284 eq45
    | exact resolve eq45 eq52284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52284
  have eq52453 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq52411
    | exact resolve eq52411 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52411
  have eq52548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq52453 eq68
    | (have j0 := eq68 (σ x) (σ y)
       grind)
    | exact resolve eq68 eq52453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52453
  have eq52560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq52548
    | exact resolve eq52548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52548
  have eq52567 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq52560
       have r₂ := eq28
       grind)
    | exact resolve eq52560 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52560
  have eq52634 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq52567 eq23333
    | exact resolve eq23333 eq52567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23333 eq52567
  have eq52688 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq52634
  have eq53227 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq52688 eq2533
    | exact resolve eq2533 eq52688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52688
  have eq53260 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq53227
    | exact resolve eq53227 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53227
  have eq53523 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq53260 eq232
    | exact resolve eq232 eq53260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq53260
  have eq60807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq46047 eq102
    | exact resolve eq102 eq46047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq46047
  have eq60925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq60807
    | exact resolve eq60807 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60807
  have eq60940 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq60925
       have r₂ := eq28
       grind)
    | exact resolve eq60925 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60925
  have eq61315 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq60940
       grind)
    | exact superpose eq60940 eq54
    | exact resolve eq54 eq60940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60940
  have eq61353 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq61315
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61315
    | exact resolve eq61315 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61315
  have eq61354 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq61353
  have eq61359 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61354 eq27
    | exact resolve eq27 eq61354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61361 : ∀ X0 : G, (σ (k y X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq61354 eq37
    | exact resolve eq37 eq61354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq61365 : (k x y) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61354 eq60
    | exact resolve eq60 eq61354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq61459 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61354 eq18826
    | exact resolve eq18826 eq61354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18826 eq61354
  have eq61552 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq61459
  have eq61567 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq61552
       have r₂ := eq711
       grind)
    | exact resolve eq61552 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61552
  have eq61591 : (k x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64 eq61365
    | exact resolve eq61365 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61365
  have eq61595 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38 eq61361
    | exact resolve eq61361 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq61361
  have eq61810 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq61567 eq51
    | exact resolve eq51 eq61567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq62011 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq62318 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61359 eq2533
    | exact resolve eq2533 eq61359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533
  have eq64755 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq707 eq62318
    | exact resolve eq62318 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62318
  have eq64788 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq64755
  have eq66637 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64788 eq61359
    | exact resolve eq61359 eq64788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61359 eq64788
  have eq66666 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq66637
  have eq66692 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66666 eq240
    | exact resolve eq240 eq66666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq66714 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq66666 eq4539
    | exact resolve eq4539 eq66666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4539 eq66666
  have eq66724 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq66714 X0
       grind)
    | (have r₁ := eq66714 X0
       have r₂ := eq28
       grind)
    | exact resolve eq66714 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66714
  have eq66728 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq66692
       have r₂ := eq28
       grind)
    | exact resolve eq66692 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66692
  have eq67962 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq707 eq66728
    | exact resolve eq66728 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq66728
  have eq67969 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq67962
  have eq68617 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq67969 eq64
    | exact resolve eq64 eq67969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq67969
  have eq68633 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq68617
    | exact resolve eq68617 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq68617
  have eq69203 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq68633 eq61591
    | exact resolve eq61591 eq68633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61591 eq68633
  have eq69211 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq69203
  have eq69544 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq69211
       grind)
    | exact superpose eq69211 eq45
    | exact resolve eq45 eq69211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq69211
  have eq69588 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq69544
    | exact resolve eq69544 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69544
  have eq69834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq69588 eq68
    | (have j0 := eq68 (σ x) (σ y)
       grind)
    | exact resolve eq68 eq69588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq69588
  have eq69851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq69834
    | exact resolve eq69834 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69834
  have eq69857 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq69851
       have r₂ := eq28
       grind)
    | exact resolve eq69851 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69851
  have eq69922 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq69857 eq56
    | exact resolve eq56 eq69857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq69857
  have eq93274 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq61595 eq39
    | exact resolve eq39 eq61595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq61595
  have eq93429 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq93274
    | (have j0 := eq93274 X0
       grind)
    | exact resolve eq93274 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93274
  have eq93508 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq93429 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq93429
    | exact resolve eq93429 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq93429
  have eq95155 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61810 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61810
    | (have j0 := eq61810 x
       grind)
    | exact resolve eq61810 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61810
  have eq95448 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17636 eq95155
    | exact resolve eq95155 eq17636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17636 eq95155
  have eq95513 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq95448
  have eq95516 : x = (M.op y (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq95513
       have r₂ := eq62011
       grind)
    | exact resolve eq95513 eq62011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95513
  have eq95567 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 (M.op x x)
       have i₂ := eq95516
       grind)
    | exact superpose eq95516 eq14
    | exact resolve eq14 eq95516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95516
  have eq133915 : (σ (M.op x y)) = (M.op (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq53523 eq66724
    | exact resolve eq66724 eq53523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53523 eq66724
  have eq133954 : (σ (M.op x y)) = (M.op (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq133915
  have eq134004 : (σ (M.op x y)) = (M.op (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq133954
       have r₂ := eq62011
       grind)
    | exact resolve eq133954 eq62011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62011 eq133954
  have eq153485 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5483 x (M.op y y)
       have i₂ := eq95567 x
       grind)
    | exact superpose eq95567 eq5483
    | exact resolve eq5483 eq95567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5483 eq95567
  have eq153891 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq153485
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq153485
    | exact resolve eq153485 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153485
  have eq153995 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq153891
       grind)
    | exact superpose eq153891 eq54
    | exact resolve eq54 eq153891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq153998 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq236 y x
       have i₂ := eq153891
       grind)
    | exact superpose eq153891 eq236
    | exact resolve eq236 eq153891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq153891
  have eq154047 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq153998 X0
       grind)
    | (have r₁ := eq153998 X0
       have r₂ := eq61567
       grind)
    | exact resolve eq153998 eq61567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61567 eq153998
  have eq157858 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq154047 eq75
    | exact resolve eq75 eq154047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq154047
  have eq173252 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq153995 eq157858
    | exact resolve eq157858 eq153995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153995 eq157858
  have eq173391 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq173252
  have eq173398 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq173391
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq173391
    | exact resolve eq173391 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173391
  have eq173432 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq173398 eq93508
    | exact resolve eq93508 eq173398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93508 eq173398
  have eq173440 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq173432
  have eq173553 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq173440 eq134004
    | exact resolve eq134004 eq173440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134004 eq173440
  have eq173579 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq173553
  have eq176387 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq173579 eq69922
    | exact resolve eq69922 eq173579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69922 eq173579
  have eq176496 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq176387
  have eq176530 : x = (M.op x y) := by
    first
    | (have r₁ := eq176496
       have r₂ := eq711
       grind)
    | exact resolve eq176496 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq176496
  have eq176550 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq176530 eq21
    | exact resolve eq21 eq176530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq176982 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq176550
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq176550
    | exact resolve eq176550 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176550
  have eq176987 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq176982 eq27
    | exact resolve eq27 eq176982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq177119 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq176982 eq22723
    | (have r₁ := eq22723
       have r₂ := eq176982
       grind)
    | exact resolve eq22723 eq176982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22723
  have eq177286 : x = y := by grind
  clear eq177119
  have eq177343 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq177286
       grind)
    | exact superpose eq177286 eq19
    | exact resolve eq19 eq177286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq177344 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq177286
       grind)
    | exact superpose eq177286 eq25
    | exact resolve eq25 eq177286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq177434 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq764 X0
       have i₂ := eq177286
       grind)
    | exact superpose eq177286 eq764
    | (have r₁ := eq764 X0
       have r₂ := eq177286
       grind)
    | exact resolve eq764 eq177286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq177286
  have eq177730 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq177434 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177434
  have eq177879 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq176982 eq177730
    | (have j0 := eq177730 X0
       grind)
    | exact resolve eq177730 eq176982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177730
  have eq177964 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq177344
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq177344
    | exact resolve eq177344 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177344
  have eq177965 : x = (M.op x x) := by
    first
    | exact superpose eq176530 eq177343
    | exact resolve eq177343 eq176530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176530 eq177343
  have eq178093 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq177879 X0
       grind)
    | (have r₁ := eq177879 X0
       have r₂ := eq28
       grind)
    | exact resolve eq177879 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177879
  have eq178174 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq176982 eq177964
    | exact resolve eq177964 eq176982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177964
  have eq178700 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq178174 eq176987
    | exact resolve eq176987 eq178174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176987 eq178174
  have eq183029 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq370 x
       have i₂ := eq178093 x
       grind)
    | exact superpose eq178093 eq370
    | (have j0 := eq370 x
       grind)
    | exact resolve eq370 eq178093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq178093
  have eq183284 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq183029
       have i₂ := eq177965
       grind)
    | exact superpose eq177965 eq183029
    | exact resolve eq183029 eq177965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177965 eq183029
  have eq183285 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq183284
  have eq183485 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq183285
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq183285
    | exact resolve eq183285 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq183285
  have eq183646 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq176982 eq183485
    | exact resolve eq183485 eq176982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176982 eq183485
  have eq183788 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq178700 eq183646
    | exact resolve eq183646 eq178700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178700 eq183646
  have eq183913 : False := by grind
  exact eq183913

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
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
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq48 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq49 (σ X0)
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq57
    | exact resolve eq57 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq57
  have eq75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq102 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq234 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq249 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq234 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq258 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq249 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq249 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq272 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq258 X0 X1
       have j1 := eq102 X0 (σ X1)
       grind)
    | (have r₁ := eq258 X0 X1
       have r₂ := eq102 X0 X1
       grind)
    | exact resolve eq258 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq258
  have eq282 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq272
    | (have j0 := eq272 X0 X1
       grind)
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq283 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq288 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq283 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq283
    | exact resolve eq283 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq283 x y
       grind)
    | exact superpose eq283 eq16
    | exact resolve eq16 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq607 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq288 X0 (τ X1)
       grind)
    | exact superpose eq288 eq17
    | exact resolve eq17 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq288
  have eq630 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq607 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq607
    | exact resolve eq607 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq645 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq630
    | exact resolve eq630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq679 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq300
       have i₂ := eq645 x y
       grind)
    | exact superpose eq645 eq300
    | exact resolve eq300 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq645
  have eq680 : False := by grind
  exact eq680

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq67
    | (have j0 := eq67 (σ X0) (σ X1)
       grind)
    | exact resolve eq67 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq67
    | (have j0 := eq67 (σ x) (σ X0)
       grind)
    | exact resolve eq67 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq91 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x x
       grind)
    | exact superpose eq67 eq43
    | (have j1 := eq67 x x
       grind)
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq67 x y
       grind)
    | exact superpose eq67 eq44
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq44 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq114 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq53 X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq114 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103 eq67
    | (have j0 := eq67 (σ x) (σ y)
       grind)
    | exact resolve eq67 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq148 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq137 eq16
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq222 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op X1 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq362 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq117
    | (have r₁ := eq117
       have r₂ := eq127
       grind)
    | exact resolve eq117 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq363 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq362
  have eq366 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq363 eq103
    | exact resolve eq103 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq369 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq366
  have eq375 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq369 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq369
       grind)
    | exact resolve eq13 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq379 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq411 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0)
       have i₂ := eq85 X0 X0
       grind)
    | exact superpose eq85 eq53
    | (have j1 := eq85 X0 (k X0 X0)
       grind)
    | exact resolve eq53 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq482 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0) X0 X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y x X0 X1
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq52
  have eq720 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq55 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 y x
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ y) (σ x)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq379 eq103
    | exact resolve eq103 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq379
  have eq895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq891
  have eq900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq895
    | exact resolve eq895 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq902 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq900
       have r₂ := eq27
       grind)
    | exact resolve eq900 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq924 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) X1)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq902 eq14
    | exact resolve eq14 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq902 eq55
    | exact resolve eq55 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2254 : ∀ X0 : G, (σ x) ≠ (σ (k x X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq2631 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq222 X0 sF0
       have i₂ := eq55 sF0 sF0
       grind)
    | exact superpose eq55 eq222
    | exact resolve eq222 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq2662 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq902 eq226
    | exact resolve eq226 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq3279 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq415 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq415
    | (have j0 := eq415 x y
       grind)
    | exact resolve eq415 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq415
  have eq3302 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3279
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3279
    | exact resolve eq3279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279
  have eq3326 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3302
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3302
    | exact resolve eq3302 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3302
  have eq3347 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3326
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3326
    | exact resolve eq3326 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326
  have eq3356 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3347
    | exact resolve eq3347 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3347
  have eq3509 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq504 X0 X0 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq504
    | exact resolve eq504 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq4435 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2662 sF4
       have i₂ := eq55 sF4 sF4
       grind)
    | exact superpose eq55 eq2662
    | exact resolve eq2662 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq4471 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4435 eq14
    | exact resolve eq14 eq4435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4435
  have eq5060 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq507 x X1 X0
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq507
    | exact resolve eq507 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq5363 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq411 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq411
    | (have j0 := eq411 (τ X0)
       grind)
    | exact resolve eq411 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq411
  have eq5384 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5363 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5363
    | (have j0 := eq5363 X0
       grind)
    | exact resolve eq5363 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5363
  have eq5393 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5384 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5384
    | (have j0 := eq5384 X0
       grind)
    | exact resolve eq5384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5384
  have eq5400 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq496 (M.op y X0) X0
       have i₂ := eq55 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq55 eq496
    | exact resolve eq496 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq5425 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X2 (M.op X0 (M.op (σ y) X1))) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq499 eq4471
    | exact resolve eq4471 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq4471
  have eq5879 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) X2))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq902 eq506
    | exact resolve eq506 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5893 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq506 X0 X0 X2 X3 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq506
    | exact resolve eq506 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq5914 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq118 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq118
    | (have j0 := eq118 X0
       grind)
    | exact resolve eq118 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq118
  have eq5920 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq925 eq5914
    | exact resolve eq5914 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq5943 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5920
       have r₂ := eq129
       grind)
    | exact resolve eq5920 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5920
  have eq5958 : (τ (σ x)) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5943 eq148
    | exact resolve eq148 eq5943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq5943
  have eq5963 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq5958
    | exact resolve eq5958 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5958
  have eq5972 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq5963
       have i₂ := eq67 sF0 x
       grind)
    | exact superpose eq67 eq5963
    | (have j1 := eq67 (M.op x y) x
       grind)
    | exact resolve eq5963 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5963
  have eq7760 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5879 (M.op sF2 x) (M.op sF2 x) x
       have i₂ := eq53 (M.op sF2 x)
       grind)
    | exact superpose eq53 eq5879
    | exact resolve eq5879 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5879
  have eq7847 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq7760 (M.op (M.op X1 (M.op (M.op sF2 sF2) x)) (M.op X1 (M.op (M.op sF2 sF2) x)))
       have i₂ := eq482 sF2 X1 x
       grind)
    | exact superpose eq482 eq7760
    | exact resolve eq7760 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq7760
  have eq8625 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq505 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq53 (M.op X1 X2)
       grind)
    | exact superpose eq53 eq505
    | exact resolve eq505 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq13159 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq724
    | exact resolve eq724 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13193 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13159 eq924
    | exact resolve eq924 eq13159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924 eq13159
  have eq13231 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13193
  have eq13392 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13231
    | (have j0 := eq13231 (σ x)
       grind)
    | exact resolve eq13231 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13231
  have eq16300 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq5972 eq3509
    | exact resolve eq3509 eq5972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3509
  have eq17004 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq5972 eq16300
    | exact resolve eq16300 eq5972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5972 eq16300
  have eq17028 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq17004
  have eq17039 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq17028
       grind)
    | exact superpose eq17028 eq53
    | exact resolve eq53 eq17028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17028
  have eq17071 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq17039 eq2631
    | exact resolve eq2631 eq17039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq17145 : (M.op x y) = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq17071 eq53
    | exact resolve eq53 eq17071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17071
  have eq18740 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq17145 eq5060
    | exact resolve eq5060 eq17145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5060 eq17145
  have eq20900 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq18740 eq17039
    | exact resolve eq17039 eq18740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17039 eq18740
  have eq20923 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq20900
  have eq31039 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5425 (M.op sF3 x) x (M.op sF3 x)
       have i₂ := eq53 (M.op sF3 x)
       grind)
    | exact superpose eq53 eq5425
    | exact resolve eq5425 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5425
  have eq31173 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31039 (M.op sF3 sF3)
       have i₂ := eq53 sF3
       grind)
    | exact superpose eq53 eq31039
    | exact resolve eq31039 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31039
  have eq31261 : (σ x) = (M.op (σ y) (M.op (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq31173
    | exact resolve eq31173 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31173
  have eq31337 : (σ x) = (M.op (σ y) (M.op (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq31261
  have eq31383 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31337 eq14
    | exact resolve eq14 eq31337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31337
  have eq31931 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31383 eq7847
    | exact resolve eq7847 eq31383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7847 eq31383
  have eq31987 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31931
  have eq38336 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31987 eq744
    | exact resolve eq744 eq31987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq31987
  have eq42549 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13392 eq38336
    | exact resolve eq38336 eq13392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13392 eq38336
  have eq42617 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq42549
  have eq42656 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq42617
    | exact resolve eq42617 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42617
  have eq42692 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42656 eq724
    | exact resolve eq724 eq42656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq42656
  have eq43223 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq42692
    | exact resolve eq42692 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq42692
  have eq43345 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq43223
  have eq45256 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43345 eq902
    | exact resolve eq902 eq43345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43345
  have eq45437 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq45256
  have eq45458 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45437 eq29
    | exact resolve eq29 eq45437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq45437
  have eq45638 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq45458
    | exact resolve eq45458 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq45458
  have eq46208 : x = (M.op x y) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45638 eq20923
    | exact resolve eq20923 eq45638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20923
  have eq46237 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq45638
  have eq46241 : x = (M.op x y) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46208
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq46208
    | exact resolve eq46208 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46208
  have eq46242 : x = (M.op x y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq46241
  have eq66409 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq46242
       have r₂ := eq46237
       grind)
    | exact resolve eq46242 eq46237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46237 eq46242
  have eq66428 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq742 x x
       have i₂ := eq66409
       grind)
    | exact superpose eq66409 eq742
    | (have r₁ := eq742 x x
       have r₂ := eq66409
       grind)
    | exact resolve eq742 eq66409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66451 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq66428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66428
  have eq68809 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66451 x
       grind)
    | exact superpose eq66451 eq43
    | exact resolve eq43 eq66451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66451
  have eq83029 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68809
       have i₂ := eq66409
       grind)
    | exact superpose eq66409 eq68809
    | exact resolve eq68809 eq66409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66409 eq68809
  have eq83114 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq83029
  have eq83118 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq83114
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq83114
    | exact resolve eq83114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83114
  have eq83138 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq83118 eq67
    | (have j0 := eq67 (σ x) (σ x)
       grind)
    | exact resolve eq67 eq83118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq83118
  have eq83150 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq83138
  have eq83181 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq83150 eq902
    | exact resolve eq902 eq83150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq83150
  have eq83383 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq83181
  have eq83408 : x = (M.op x y) := by
    first
    | (have r₁ := eq83383
       have r₂ := eq129
       grind)
    | exact resolve eq83383 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq83383
  have eq83688 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq83408 eq20
    | exact resolve eq20 eq83408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq83746 : y = (M.op x (M.op y y)) := by
    first
    | exact superpose eq83408 eq720
    | exact resolve eq720 eq83408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq83864 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq83688
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq83688
    | exact resolve eq83688 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83688
  have eq83867 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq83864 eq26
    | exact resolve eq26 eq83864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83963 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq83864 eq3356
    | exact resolve eq3356 eq83864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356
  have eq84155 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq83963
       have r₂ := eq27
       grind)
    | exact resolve eq83963 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83963
  have eq84276 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (M.op y X0) (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq8625 y X0 x y
       have i₂ := eq83746
       grind)
    | exact superpose eq83746 eq8625
    | exact resolve eq8625 eq83746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8625
  have eq84297 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq5893 x X0 X1 (M.op y y)
       have i₂ := eq83746
       grind)
    | exact superpose eq83746 eq5893
    | exact resolve eq5893 eq83746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5893 eq83746
  have eq84311 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq84276 X0
       have i₂ := eq5400 X0
       grind)
    | exact superpose eq5400 eq84276
    | exact resolve eq84276 eq5400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5400 eq84276
  have eq84313 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op x (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq83408 eq84311
    | exact resolve eq84311 eq83408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84311
  have eq90439 : (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq84297 y y
       have i₂ := eq53 y
       grind)
    | exact superpose eq53 eq84297
    | exact resolve eq84297 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84297
  have eq90986 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq84313 (M.op y y)
       have i₂ := eq53 y
       grind)
    | exact superpose eq53 eq84313
    | exact resolve eq84313 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq84313
  have eq91066 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq90986
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90986
    | exact resolve eq90986 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq90986
  have eq91078 : y = (M.op y x) := by
    first
    | exact superpose eq83408 eq91066
    | exact resolve eq91066 eq83408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83408 eq91066
  have eq91084 : y = (M.op x x) := by
    first
    | (have i₁ := eq91078
       have i₂ := eq90439
       grind)
    | exact superpose eq90439 eq91078
    | exact resolve eq91078 eq90439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90439 eq91078
  have eq91091 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq91084
       grind)
    | exact superpose eq91084 eq91
    | exact resolve eq91 eq91084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq91116 : ∀ X0 : G, x ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq742 x x
       have i₂ := eq91084
       grind)
    | exact superpose eq91084 eq742
    | exact resolve eq742 eq91084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91119 : y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5914 x
       have i₂ := eq91084
       grind)
    | exact superpose eq91084 eq5914
    | exact resolve eq5914 eq91084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5914
  have eq91159 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq83864 eq91091
    | exact resolve eq91091 eq83864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91091
  have eq91162 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq91159
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91159
    | exact resolve eq91159 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91159
  have eq92272 : (σ y) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2254 y
       have i₂ := eq91119
       grind)
    | exact superpose eq91119 eq2254
    | (have j0 := eq2254 y
       grind)
    | exact resolve eq2254 eq91119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254 eq91119
  have eq92289 : (σ y) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq83864 eq92272
    | exact resolve eq92272 eq83864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92272
  have eq92313 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq92289
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq92289
    | exact resolve eq92289 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92289
  have eq92336 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq92313
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq92313
    | exact resolve eq92313 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92313
  have eq92350 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq92336
    | exact resolve eq92336 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq92336
  have eq92360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq83864 eq92350
    | exact resolve eq92350 eq83864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92350
  have eq92368 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have r₁ := eq92360
       have r₂ := eq27
       grind)
    | exact resolve eq92360 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92360
  have eq92523 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq91162 eq5393
    | (have j0 := eq5393 (σ (M.op x y))
       grind)
    | exact resolve eq5393 eq91162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5393
  have eq92537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq83867 eq92523
    | exact resolve eq92523 eq83867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83867 eq92523
  have eq92542 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq92537
       have r₂ := eq27
       grind)
    | exact resolve eq92537 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq92537
  have eq92921 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq92542 eq742
    | (have r₁ := eq742 (σ (M.op x y)) x
       have r₂ := eq92542
       grind)
    | exact resolve eq742 eq92542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq92948 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq92921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92921
  have eq95568 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq92948 eq91162
    | exact resolve eq91162 eq92948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91162 eq92948
  have eq95690 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq95568
  have eq95815 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq95690 eq92542
    | exact resolve eq92542 eq95690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92542 eq95690
  have eq95904 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq95815
  have eq95910 : x = y := by
    first
    | (have r₁ := eq95904
       have r₂ := eq92368
       grind)
    | exact resolve eq95904 eq92368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92368 eq95904
  have eq95922 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq95910
       grind)
    | exact superpose eq95910 eq24
    | exact resolve eq24 eq95910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96089 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq91116 X0
       have i₂ := eq95910
       grind)
    | exact superpose eq95910 eq91116
    | (have r₁ := eq91116 X0
       have r₂ := eq95910
       grind)
    | exact resolve eq91116 eq95910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91116 eq95910
  have eq96095 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq96089 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96089
  have eq96203 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq95922
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95922
    | exact resolve eq95922 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq95922
  have eq96291 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq83864 eq96203
    | exact resolve eq96203 eq83864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96203
  have eq96508 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq96291 eq84155
    | exact resolve eq84155 eq96291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84155
  have eq97124 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq96095 x
       grind)
    | exact superpose eq96095 eq43
    | exact resolve eq43 eq96095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq96095
  have eq97348 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq97124
       have i₂ := eq91084
       grind)
    | exact superpose eq91084 eq97124
    | exact resolve eq97124 eq91084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91084 eq97124
  have eq97475 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq83864 eq97348
    | exact resolve eq97348 eq83864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83864 eq97348
  have eq97580 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq97475
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq97475
    | exact resolve eq97475 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq97475
  have eq97675 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq96291 eq97580
    | exact resolve eq97580 eq96291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96291 eq97580
  have eq97751 : False := by grind
  exact eq97751

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq62 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 X0)
       have i₂ := eq64 X0 X2
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq72
    | exact resolve eq72 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq141 (τ X0)
       grind)
    | exact superpose eq141 eq18
    | (have j1 := eq141 (τ X0)
       grind)
    | exact resolve eq18 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq150 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq150
    | (have j0 := eq150 X0
       grind)
    | exact resolve eq150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq166 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq153 X0
       grind)
    | exact superpose eq153 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq153 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq153 X0
       grind)
    | exact resolve eq12 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq171 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq166 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq269 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq171 (σ X0) X1
       grind)
    | exact superpose eq171 eq22
    | (have j1 := eq171 (σ X0) X1
       grind)
    | exact resolve eq22 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq276 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq269 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq269
    | (have j0 := eq269 X0 X1
       grind)
    | exact resolve eq269 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq285 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq276
    | (have j0 := eq276 X0 X1
       grind)
    | exact resolve eq276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq315 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq285 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq317 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq315 X0
       have j1 := eq141 X0
       grind)
    | (have r₁ := eq315 X0
       have r₂ := eq141 X0
       grind)
    | exact resolve eq315 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq315
  have eq577 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq70 X1 X1 X0
       grind)
    | exact superpose eq70 eq72
    | exact resolve eq72 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq583 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X3 X1) (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X1) X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq70 X1 X3 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq14 X0 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X2 X0
       have j1 := eq14 X2 X0
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq64 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq88 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq88
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq88 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq62 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq647 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq636 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq649 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq648 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq651 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq647 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq647 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq647 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq661 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq649 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq649 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq649 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq666 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq629 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq629 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq629 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq672 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq623 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq623 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq623 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq675 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq620 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq620 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq620 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq681 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq591 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq591 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq591 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq591 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq684 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq681 X0 X1 X2
       have j1 := eq651 X0 X2
       grind)
    | (have r₁ := eq681 X0 X1 X2
       have r₂ := eq651 X0 X1
       grind)
    | exact resolve eq681 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq721 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq651 X0 (M.op X0 X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq651
    | (have j0 := eq651 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq651 X0 (M.op X0 X0)
       have r₂ := eq62 X0
       grind)
    | exact resolve eq651 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq721 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq724 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq722 X0
       have i₂ := eq88 X0 X0
       grind)
    | exact superpose eq88 eq722
    | exact resolve eq722 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq726 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq724 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq724
    | exact resolve eq724 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq726 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq726
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq726 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq742 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq742 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq742 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq886 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq661 X1 (τ X0)
       grind)
    | exact superpose eq661 eq17
    | (have j1 := eq661 X1 (τ X0)
       grind)
    | exact resolve eq17 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq661 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq1031 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq577 X0 X1 X0
       have i₂ := eq666 X0 X1
       grind)
    | exact superpose eq666 eq577
    | (have j1 := eq666 X0 X1
       grind)
    | exact resolve eq577 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 (M.op X0 X1)
       have i₂ := eq666 X0 X1
       grind)
    | exact superpose eq666 eq651
    | (have j0 := eq651 X0 (M.op X0 X1)
       have j1 := eq666 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq651 X0 (M.op X0 X1)
       have r₂ := eq666 X0 X1
       grind)
    | exact resolve eq651 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1041 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1132 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1
       have i₂ := eq1031 X0 X1
       grind)
    | (have i₁ := eq62 X1
       have i₂ := eq1031 X1 X1
       grind)
    | exact superpose eq1031 eq62
    | (have j1 := eq1031 X0 X1
       grind)
    | exact resolve eq62 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq1031 X1 X0
       grind)
    | (have i₁ := eq14 X1 X1
       have i₂ := eq1031 X0 X1
       grind)
    | exact superpose eq1031 eq14
    | (have j0 := eq14 X0 X1
       have j1 := eq1031 X1 X0
       grind)
    | exact resolve eq14 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1154 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq651 X1 X0
       have i₂ := eq1031 X1 X0
       grind)
    | (have i₁ := eq651 X1 X1
       have i₂ := eq1031 X0 X1
       grind)
    | exact superpose eq1031 eq651
    | (have j0 := eq651 X1 X0
       have j1 := eq1031 X1 X0
       grind)
    | (have r₁ := eq651 (M.op X1 X1) X1
       have r₂ := eq1031 (M.op X1 X1) X1
       grind)
    | exact resolve eq651 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1155 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq666 X1 X0
       have i₂ := eq1031 X1 X0
       grind)
    | (have i₁ := eq666 X1 X1
       have i₂ := eq1031 X0 X1
       grind)
    | exact superpose eq1031 eq666
    | (have j0 := eq666 X1 X0
       have j1 := eq1031 X1 X0
       grind)
    | exact resolve eq666 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq1156 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq762 X1 X0
       have i₂ := eq1031 X1 X0
       grind)
    | (have i₁ := eq762 X1 X1
       have i₂ := eq1031 X0 X1
       grind)
    | exact superpose eq1031 eq762
    | (have j0 := eq762 X1 X0
       have j1 := eq1031 X1 X0
       grind)
    | exact resolve eq762 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq1157 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq894 X1 X0
       have i₂ := eq1031 X1 X0
       grind)
    | (have i₁ := eq894 X1 X1
       have i₂ := eq1031 X0 X1
       grind)
    | exact superpose eq1031 eq894
    | (have j0 := eq894 X0 X0
       have j1 := eq1031 X1 X0
       grind)
    | exact resolve eq894 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1194 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1156 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1195 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1155 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1196 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1154 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1197 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1200 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1197 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1197 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq1197 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq1197 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1197 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1308 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1132 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq1132 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq1132
    | (have j0 := eq1132 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq1132 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1361 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1367 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1361 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1361 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq1361 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1361 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq1466 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X1
       have i₂ := eq1195 X1 X0
       grind)
    | exact superpose eq1195 eq9
    | (have j1 := eq1195 X1 X0
       grind)
    | exact resolve eq9 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1634 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X0
       have i₂ := eq1200 X0 X1
       grind)
    | (have i₁ := eq64 X1 X1
       have i₂ := eq1200 X0 X1
       grind)
    | exact superpose eq1200 eq64
    | (have j1 := eq1200 X0 X1
       grind)
    | exact resolve eq64 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1708 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1634 X0 X1
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq1634
    | (have j0 := eq1634 X0 X1
       grind)
    | exact resolve eq1634 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634
  have eq1740 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq1708 X0 (σ X1)
       grind)
    | exact superpose eq1708 eq22
    | (have j1 := eq1708 (k (τ X0) X1) (τ (M.op X0 (σ X1)))
       grind)
    | exact resolve eq22 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1747 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1708 X0 (τ X1)
       grind)
    | exact superpose eq1708 eq18
    | (have j1 := eq1708 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1753 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1708 (σ X0) (σ X1)
       grind)
    | exact superpose eq1708 eq15
    | (have j1 := eq1708 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1875 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq577 X1 X1 X0
       have i₂ := eq1367 X1 X0
       grind)
    | exact superpose eq1367 eq577
    | (have j1 := eq1367 X1 X0
       grind)
    | exact resolve eq577 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq2104 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1740 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1740
    | exact resolve eq1740 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq2142 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2104 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq2104
    | (have j0 := eq2104 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq2104 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2104
  have eq2147 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2142 (M.op X1 X1) X0
       have i₂ := eq1194 X1 X0
       grind)
    | exact superpose eq1194 eq2142
    | (have j0 := eq2142 (τ X0) (τ (M.op X0 (M.op X1 X1)))
       have j1 := eq1194 X1 X0
       grind)
    | exact resolve eq2142 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142
  have eq2200 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2147 X0 X1
       have j1 := eq1196 X1 X0
       grind)
    | (have r₁ := eq2147 X1 X0
       have r₂ := eq1196 X0 X1
       grind)
    | (have r₁ := eq2147 (M.op X0 X0) X1
       have r₂ := eq1196 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq2147 X0 X0
       have r₂ := eq1196 X0 (k X0 X0)
       grind)
    | exact resolve eq2147 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2147
  have eq2202 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1747 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1747
    | exact resolve eq1747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747
  have eq2221 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2202 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2202
    | (have j0 := eq2202 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq2202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2226 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2221 (M.op X1 X1) X0
       have i₂ := eq1194 X1 X0
       grind)
    | exact superpose eq1194 eq2221
    | (have j0 := eq2221 (σ X0) (σ (M.op X0 (M.op X1 X1)))
       have j1 := eq1194 X1 X0
       grind)
    | exact resolve eq2221 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq2221
  have eq2268 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2226 X0 X1
       have j1 := eq1196 X1 X0
       grind)
    | (have r₁ := eq2226 X1 X0
       have r₂ := eq1196 X0 X1
       grind)
    | (have r₁ := eq2226 (M.op X0 X0) X1
       have r₂ := eq1196 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq2226 X0 X0
       have r₂ := eq1196 X0 (k X0 X0)
       grind)
    | exact resolve eq2226 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226
  have eq2505 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1875 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq1875 X0 X1
       grind)
    | exact superpose eq1875 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq1875 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq1875 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq1875 X1 X1
       grind)
    | exact resolve eq13 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2572 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2505 X0 X1
       have j1 := eq1200 X1 X0
       grind)
    | (have r₁ := eq2505 X0 X1
       have r₂ := eq1200 X0 X1
       grind)
    | (have r₁ := eq2505 X1 X0
       have r₂ := eq1200 X0 X1
       grind)
    | exact resolve eq2505 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200 eq2505
  have eq2584 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2572 X0 X1
       have j1 := eq1157 X1 X0
       grind)
    | (have r₁ := eq2572 X0 X0
       have r₂ := eq1157 X0 X1
       grind)
    | exact resolve eq2572 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157 eq2572
  have eq2632 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq2584 X1 (σ X0)
       grind)
    | exact superpose eq2584 eq22
    | (have j1 := eq2584 X1 (σ X0)
       grind)
    | exact resolve eq22 eq2584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2702 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2632 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2632
    | (have j0 := eq2632 X0 X1
       grind)
    | exact resolve eq2632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632
  have eq3026 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (M.op X0 X0) X1 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq87
    | exact resolve eq87 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3045 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq87
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3048 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op X3 (M.op X2 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (M.op X0 X1) (M.op X0 X1) X2
       have i₂ := eq87 X0 X1 X2
       grind)
    | (have i₁ := eq87 (M.op X2 X0) (M.op X0 X1) X2
       have i₂ := eq87 X0 X1 X2
       grind)
    | exact superpose eq87 eq87
    | exact resolve eq87 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3163 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X3 (M.op X2 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3048 X0 X1 X2 X3
       have i₂ := eq583 X0 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq583 eq3048
    | exact resolve eq3048 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq3048
  have eq3187 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3045 (M.op X1 (M.op X0 X2)) X4 (M.op X0 X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq3045
    | exact resolve eq3045 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3233 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3045 X0 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq62 (M.op X0 X1)
       grind)
    | exact superpose eq62 eq3045
    | exact resolve eq3045 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3299 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 X1
       have i₂ := eq3233 X0 X1
       grind)
    | exact superpose eq3233 eq672
    | (have j0 := eq672 X0 X1
       grind)
    | exact resolve eq672 eq3233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq3300 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1054 X0 X1
       have i₂ := eq3233 X0 X1
       grind)
    | exact superpose eq3233 eq1054
    | (have j0 := eq1054 X0 X1
       grind)
    | exact resolve eq1054 eq3233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq3332 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3233 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq3233
    | exact resolve eq3233 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3333 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3233 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq3233
    | exact resolve eq3233 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq3336 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3233 (M.op X2 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq70 X1 X2 X0
       grind)
    | exact superpose eq70 eq3233
    | exact resolve eq3233 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq3402 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3187 X0 X1 X2 X3 X4
       have i₂ := eq3333 (M.op X0 X2) X1
       grind)
    | exact superpose eq3333 eq3187
    | exact resolve eq3187 eq3333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187
  have eq3412 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X0 X1 X2
       have i₂ := eq3333 X1 X0
       grind)
    | exact superpose eq3333 eq87
    | exact resolve eq87 eq3333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq3421 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1
       have i₂ := eq3333 X1 X0
       grind)
    | exact superpose eq3333 eq675
    | (have j0 := eq675 X0 X1
       grind)
    | exact resolve eq675 eq3333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq3446 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X3 (M.op X2 X0)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3163 X0 X1 X2 X3
       have i₂ := eq3333 X1 X0
       grind)
    | exact superpose eq3333 eq3163
    | exact resolve eq3163 eq3333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3163
  have eq3451 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3336 X0 X1 X2
       have i₂ := eq3333 X1 X2
       grind)
    | exact superpose eq3333 eq3336
    | exact resolve eq3336 eq3333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq3453 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3026 X0 X1
       have i₂ := eq3333 X1 (M.op X0 X0)
       grind)
    | exact superpose eq3333 eq3026
    | exact resolve eq3026 eq3333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3457 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3332 X0 X1 X2
       have i₂ := eq3333 (M.op X0 X2) X1
       grind)
    | exact superpose eq3333 eq3332
    | exact resolve eq3332 eq3333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332 eq3333
  have eq3507 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3402 X0 X1 X2 X3 X4
       have i₂ := eq3457 X0 X1 X2
       grind)
    | exact superpose eq3457 eq3402
    | exact resolve eq3402 eq3457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3402 eq3457
  have eq3523 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3446 X0 X1 x x
       have i₂ := eq3507 X0 X1 X1 x x
       grind)
    | exact superpose eq3507 eq3446
    | exact resolve eq3446 eq3507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446 eq3507
  have eq3903 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3523 X1 X2
       have i₂ := eq3412 X1 X2 X0
       grind)
    | (have i₁ := eq3523 X0 (M.op X2 X0)
       have i₂ := eq3412 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq3412 eq3523
    | exact resolve eq3523 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412 eq3523
  have eq4058 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3903 X0 X0 (M.op X1 X1)
       have i₂ := eq1466 X0 X1
       grind)
    | exact superpose eq1466 eq3903
    | (have j1 := eq1466 X1 X0
       grind)
    | exact resolve eq3903 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4085 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X0 (M.op X0 X1)
       have i₂ := eq3903 X2 X0 X1
       grind)
    | exact superpose eq3903 eq9
    | exact resolve eq9 eq3903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3903
  have eq4119 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4085 X0 X1 X2
       have i₂ := eq3451 X2 X0 X2
       grind)
    | exact superpose eq3451 eq4085
    | exact resolve eq4085 eq3451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451 eq4085
  have eq4542 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4119 X0 (M.op X0 X0) X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq4119
    | exact resolve eq4119 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4119
  have eq10568 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2702 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2702
    | (have j0 := eq2702 X1 (σ X0)
       grind)
    | exact resolve eq2702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq10677 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10568 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10568
    | (have j0 := eq10568 X0 X1
       grind)
    | exact resolve eq10568 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10568
  have eq12126 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq684 (σ x) X0 (σ y)
       grind)
    | (have i₁ := eq16
       have i₂ := eq684 (σ x) (σ y) X0
       grind)
    | exact superpose eq684 eq16
    | (have j1 := eq684 (σ x) X0 X0
       grind)
    | exact resolve eq16 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq12264 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12126 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12126
    | (have j0 := eq12126 X0
       grind)
    | exact resolve eq12126 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12126
  have eq13101 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10677 X1 X0
       have i₂ := eq2584 X1 X0
       grind)
    | exact superpose eq2584 eq10677
    | (have j0 := eq10677 X1 X0
       have j1 := eq2584 X1 X0
       grind)
    | exact resolve eq10677 eq2584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2584 eq10677
  have eq13160 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101
  have eq13830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13160 x y
       grind)
    | exact superpose eq13160 eq16
    | (have j1 := eq13160 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq13160 x y
       grind)
    | exact resolve eq16 eq13160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13160
  have eq13937 : x = (k y x) := by grind
  clear eq13830
  have eq13963 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12264 X0
       have i₂ := eq13937
       grind)
    | exact superpose eq13937 eq12264
    | (have j0 := eq12264 X0
       grind)
    | exact resolve eq12264 eq13937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12264
  have eq13993 : x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1708 y x
       have i₂ := eq13937
       grind)
    | exact superpose eq13937 eq1708
    | (have j0 := eq1708 x (M.op y x)
       grind)
    | exact resolve eq1708 eq13937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13999 : x = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3299 x y
       have i₂ := eq13937
       grind)
    | exact superpose eq13937 eq3299
    | (have j0 := eq3299 x y
       grind)
    | exact resolve eq3299 eq13937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3299 eq13937
  have eq14022 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op X0 (M.op X1 x)) y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq3045 y X1 x X0
       have i₂ := eq13993
       grind)
    | exact superpose eq13993 eq3045
    | exact resolve eq3045 eq13993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq14028 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3233 y x
       have i₂ := eq13993
       grind)
    | exact superpose eq13993 eq3233
    | exact resolve eq3233 eq13993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3233
  have eq15413 : y = (M.op x x) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3421 y x
       have i₂ := eq13999
       grind)
    | exact superpose eq13999 eq3421
    | (have j0 := eq3421 y x
       grind)
    | exact resolve eq3421 eq13999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13999
  have eq15444 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq1196 x y
       grind)
    | (have r₁ := eq15413
       have r₂ := eq1196 x y
       grind)
    | (have r₁ := eq15413
       have r₂ := eq1196 x (M.op x y)
       grind)
    | exact resolve eq15413 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq15413
  have eq18811 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 x) y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14022 X0 y
       have i₂ := eq13993
       grind)
    | exact superpose eq13993 eq14022
    | exact resolve eq14022 eq13993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13993 eq14022
  have eq18974 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 x) y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq18811 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18811
  have eq19022 : (M.op x (M.op y y)) = (M.op y (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq3453 x y
       have i₂ := eq18974 x
       grind)
    | exact superpose eq18974 eq3453
    | exact resolve eq3453 eq18974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3453 eq18974
  have eq19115 : y = (M.op x (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq19022
       have i₂ := eq62 y
       grind)
    | exact superpose eq62 eq19022
    | exact resolve eq19022 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19022
  have eq19120 : y = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq19115
       have i₂ := eq14028
       grind)
    | exact superpose eq14028 eq19115
    | exact resolve eq19115 eq14028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14028 eq19115
  have eq19217 : y = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq19120
  have eq22811 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq886 X1 (τ X0)
       grind)
    | exact superpose eq886 eq18
    | (have j1 := eq886 X1 (τ X0)
       grind)
    | exact resolve eq18 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq886
  have eq22819 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22811 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq22811
    | (have j0 := eq22811 X0 X1
       grind)
    | exact resolve eq22811 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22811
  have eq22838 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22819 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22819
    | (have j0 := eq22819 X0 X1
       grind)
    | exact resolve eq22819 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22819
  have eq22847 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22838 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22838
    | (have j0 := eq22838 X0 X1
       grind)
    | exact resolve eq22838 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22838
  have eq34879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1753 x y
       have i₂ := eq15444
       grind)
    | exact superpose eq15444 eq1753
    | (have j0 := eq1753 x y
       grind)
    | exact resolve eq1753 eq15444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753 eq15444
  have eq34883 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq34879
       have r₂ := eq16
       grind)
    | exact resolve eq34879 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34879
  have eq34906 : y = (M.op x (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19217
       have i₂ := eq34883
       grind)
    | exact superpose eq34883 eq19217
    | exact resolve eq19217 eq34883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19217 eq34883
  have eq35021 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34906
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq34906
    | exact resolve eq34906 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq34906
  have eq35022 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq35021
  have eq35033 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq35022
       grind)
    | exact superpose eq35022 eq10
    | exact resolve eq10 eq35022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35022
  have eq35063 : x = y ∨ x = y := by
    first
    | (have i₁ := eq35033
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35033
    | exact resolve eq35033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35033
  have eq35064 : x = y := by grind
  clear eq35063
  have eq35065 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35064
       grind)
    | exact superpose eq35064 eq16
    | exact resolve eq16 eq35064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35067 : ∀ X0 : G, (M.op (σ x) X0) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13963 X0
       have i₂ := eq35064
       grind)
    | exact superpose eq35064 eq13963
    | (have j0 := eq13963 X0
       grind)
    | exact resolve eq13963 eq35064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13963
  have eq35979 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X0) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq35067 X0
       have i₂ := eq35064
       grind)
    | exact superpose eq35064 eq35067
    | (have j0 := eq35067 X0
       grind)
    | exact resolve eq35067 eq35064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35064 eq35067
  have eq36161 : ∀ X0 : G, (M.op (σ x) X0) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq35979 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq35979 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq35979 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35979
  have eq36341 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X1))
       have i₂ := eq22847 X1 X0
       grind)
    | exact superpose eq22847 eq10
    | (have j1 := eq22847 X1 X0
       grind)
    | exact resolve eq10 eq22847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22847
  have eq36838 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (M.op (σ x) (M.op X0 (σ x))) (σ x)) = (k (M.op (σ x) (M.op X0 (σ x))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq36161 (M.op (σ x) (M.op X0 (σ x)))
       have i₂ := eq4542 (σ x) X0
       grind)
    | exact superpose eq4542 eq36161
    | (have j0 := eq36161 (M.op (σ x) (M.op X0 (σ x)))
       grind)
    | exact resolve eq36161 eq4542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4542 eq36161
  have eq36883 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (M.op (σ x) (M.op X0 (σ x))) (σ x)) ∨ (M.op X0 (σ x)) ≠ (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq36838 X0
       have i₂ := eq577 X0 (σ x) (σ x)
       grind)
    | exact superpose eq577 eq36838
    | (have j0 := eq36838 X0
       grind)
    | exact resolve eq36838 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq36838
  have eq38432 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X0) X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3300 X1 X0
       have i₂ := eq1031 X1 X0
       grind)
    | (have i₁ := eq3300 X1 X1
       have i₂ := eq1031 X0 X1
       grind)
    | exact superpose eq1031 eq3300
    | (have j0 := eq3300 X1 X0
       have j1 := eq1031 X1 X0
       grind)
    | exact resolve eq3300 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq3300
  have eq38559 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X0) X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38432 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38432
  have eq42580 : ∀ X0 : G, (σ (M.op x x)) ≠ (k (M.op X0 X0) (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq35065
       have i₂ := eq38559 X0 (σ x)
       grind)
    | exact superpose eq38559 eq35065
    | (have j1 := eq38559 X0 (σ x)
       grind)
    | exact resolve eq35065 eq38559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38559
  have eq61456 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2200 X1 X0
       have i₂ := eq1466 X1 X0
       grind)
    | exact superpose eq1466 eq2200
    | (have j0 := eq2200 X1 X0
       have j1 := eq1466 X1 X0
       grind)
    | exact resolve eq2200 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq61577 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61456 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61456
  have eq61851 : ∀ X0 X1 X2 : G, (k (τ X1) (τ X0)) = (τ (k X1 X2)) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 X1
       have i₂ := eq61577 X0 X2
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq61577 X0 X1
       grind)
    | exact superpose eq61577 eq31
    | (have j1 := eq61577 X0 X2
       grind)
    | exact resolve eq31 eq61577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61577
  have eq62018 : ∀ X0 X1 X2 : G, (τ (k X1 X0)) = (τ (k X1 X2)) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61851 X0 X1 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq61851
    | (have j0 := eq61851 X0 X1 X2
       grind)
    | exact resolve eq61851 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61851
  have eq67066 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2268 X1 X0
       have i₂ := eq1466 X1 X0
       grind)
    | exact superpose eq1466 eq2268
    | (have j0 := eq2268 X1 X0
       have j1 := eq1466 X1 X0
       grind)
    | exact resolve eq2268 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq67075 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2268 X1 (M.op X0 X1)
       have i₂ := eq4058 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq4058 eq2268
    | (have j0 := eq2268 X1 (M.op X0 X1)
       have j1 := eq4058 (M.op X0 X1) X1 x
       grind)
    | exact resolve eq2268 eq4058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268 eq4058
  have eq67191 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq67075 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67075
  have eq67193 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq67066 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67066
  have eq67231 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X1) X1) ∨ (σ X1) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67191 X0 X1
       have i₂ := eq88 X1 X0
       grind)
    | exact superpose eq88 eq67191
    | (have j0 := eq67191 X0 X1
       grind)
    | exact resolve eq67191 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq67191
  have eq84861 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = (k (τ (k X0 X1)) (τ X1)) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67231 (τ X0) (τ X1)
       have i₂ := eq36341 X0 X1
       grind)
    | exact superpose eq36341 eq67231
    | (have j1 := eq36341 X0 X1
       grind)
    | exact resolve eq67231 eq36341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36341 eq67231
  have eq85068 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = (τ (k (k X0 X1) X1)) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84861 X0 X1
       have i₂ := eq31 X1 (k X0 X1)
       grind)
    | exact superpose eq31 eq84861
    | (have j0 := eq84861 X0 X1
       grind)
    | exact resolve eq84861 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq84861
  have eq85135 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (M.op (τ X1) (τ X1)) = (τ (k (k X0 X1) X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85068 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq85068
    | (have j0 := eq85068 X0 X1
       grind)
    | exact resolve eq85068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85068
  have eq85163 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op (τ X1) (τ X1)) = (τ (k (k X0 X1) X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85135 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq85135
    | (have j0 := eq85135 X0 X1
       grind)
    | exact resolve eq85135 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85135
  have eq85164 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = (τ (k (k X0 X1) X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq85163 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85163
  have eq94118 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62018 X1 X0 X0
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq62018
    | (have j0 := eq62018 X1 X1 X0
       grind)
    | exact resolve eq62018 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94460 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 X2) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 X2)
       have i₂ := eq62018 X1 X0 X2
       grind)
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq62018 X0 X1 X2
       grind)
    | exact superpose eq62018 eq11
    | (have j1 := eq62018 X1 X1 X2
       grind)
    | exact resolve eq11 eq62018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62018
  have eq94689 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 X2) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94460 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq94460
    | (have j0 := eq94460 X0 X1 X2
       grind)
    | exact resolve eq94460 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94460
  have eq95417 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq94118 X0 X1
       grind)
    | exact superpose eq94118 eq11
    | (have j1 := eq94118 X0 X1
       grind)
    | exact resolve eq11 eq94118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94118
  have eq95514 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95417 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95417
    | (have j0 := eq95417 X0 X1
       grind)
    | exact resolve eq95417 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95417
  have eq95725 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 (M.op X1 X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3421 X1 X0
       have i₂ := eq95514 X0 X1
       grind)
    | exact superpose eq95514 eq3421
    | (have j0 := eq3421 X1 X0
       have j1 := eq95514 X0 X1
       grind)
    | exact resolve eq3421 eq95514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421 eq95514
  have eq96014 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq95725 X0 X1
       have j1 := eq651 X0 X1
       grind)
    | (have r₁ := eq95725 X0 X1
       have r₂ := eq651 X0 X1
       grind)
    | (have r₁ := eq95725 X0 X0
       have r₂ := eq651 X0 (M.op X0 X0)
       grind)
    | exact resolve eq95725 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq95725
  have eq97006 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94689 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94689
  have eq97009 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97006 X0 X1
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq97006
    | (have j0 := eq97006 X0 X1
       grind)
    | exact resolve eq97006 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq97006
  have eq97585 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op X0 X1)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97009 X0 (M.op X1 X0)
       have i₂ := eq96014 X0 X1
       grind)
    | exact superpose eq96014 eq97009
    | (have j0 := eq97009 X0 X1
       have j1 := eq96014 X1 X0
       grind)
    | (have r₁ := eq97009 X1 (M.op X1 X1)
       have r₂ := eq96014 X1 X1
       grind)
    | exact resolve eq97009 eq96014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96014 eq97009
  have eq97743 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq97585 X0 X1
       have j1 := eq1708 X0 X1
       grind)
    | (have r₁ := eq97585 (k X0 X1) (M.op X0 X1)
       have r₂ := eq1708 X0 X1
       grind)
    | (have r₁ := eq97585 (M.op X0 X1) (k X0 X1)
       have r₂ := eq1708 X0 X1
       grind)
    | (have r₁ := eq97585 X0 X1
       have r₂ := eq1708 X0 X1
       grind)
    | exact resolve eq97585 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708 eq97585
  have eq199947 : ∀ X0 X1 : G, (M.op (τ (σ X1)) (τ (σ X1))) = (τ (k (σ (k X0 X1)) (σ X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85164 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85164
    | exact resolve eq85164 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199975 : ∀ X0 X1 : G, (M.op (τ (σ X1)) (τ (σ X1))) = (k (τ (σ (k X0 X1))) X1) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq199947 X0 X1
       have i₂ := eq22 (σ (k X0 X1)) X1
       grind)
    | exact superpose eq22 eq199947
    | (have j0 := eq199947 X0 X1
       grind)
    | exact resolve eq199947 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199947
  have eq199994 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq199975 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq199975
    | (have j0 := eq199975 X0 X1
       grind)
    | exact resolve eq199975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199975
  have eq199995 : ∀ X0 X1 : G, (M.op X1 X1) = (k (k X0 X1) X1) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq199994 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq199994
    | (have j0 := eq199994 X0 X1
       grind)
    | exact resolve eq199994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199994
  have eq200237 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X1 X0) X0) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67193 (k X1 X0) X0
       have i₂ := eq199995 X1 X0
       grind)
    | exact superpose eq199995 eq67193
    | (have j0 := eq67193 X0 (k X1 X0)
       have j1 := eq199995 X1 X0
       grind)
    | exact resolve eq67193 eq199995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67193 eq199995
  have eq200254 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X1 X0) X0) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq200237 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200237
  have eq200585 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op X0 X0) = (M.op (k X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq200254 X0 X1
       grind)
    | exact superpose eq200254 eq10
    | (have j1 := eq200254 X0 X1
       grind)
    | exact resolve eq10 eq200254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200254
  have eq200598 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X1 X0) X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq200585 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq200585
    | (have j0 := eq200585 X0 X1
       grind)
    | exact resolve eq200585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200585
  have eq200856 : ∀ X0 X1 : G, (k X1 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (k X1 X0) X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97743 (k X1 X0) X0
       have i₂ := eq200598 X0 X1
       grind)
    | exact superpose eq200598 eq97743
    | (have j1 := eq200598 X0 X1
       grind)
    | exact resolve eq97743 eq200598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97743 eq200598
  have eq200898 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X0) = (k (k X1 X0) X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq200856 X0 X1
       have i₂ := eq726 X0
       grind)
    | exact superpose eq726 eq200856
    | (have j0 := eq200856 X0 X1
       grind)
    | exact resolve eq200856 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq200856
  have eq200899 : ∀ X0 X1 : G, (M.op X0 X0) = (k (k X1 X0) X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq200898 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200898
  have eq201058 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85164 X1 X0
       have i₂ := eq200899 X0 X1
       grind)
    | exact superpose eq200899 eq85164
    | (have j0 := eq85164 X1 X0
       have j1 := eq200899 X0 X1
       grind)
    | exact resolve eq85164 eq200899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85164 eq200899
  have eq201167 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq201058 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201058
  have eq201464 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq201167 (σ X0) X1
       grind)
    | exact superpose eq201167 eq22
    | (have j1 := eq201167 (σ X0) X1
       grind)
    | exact resolve eq22 eq201167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq201167
  have eq201572 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq201464 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq201464
    | (have j0 := eq201464 X0 X1
       grind)
    | exact resolve eq201464 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201464
  have eq201598 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq201572 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq201572
    | (have j0 := eq201572 X0 X1
       grind)
    | exact resolve eq201572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201572
  have eq203946 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq201598 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq201598
    | (have j0 := eq201598 X1 X1
       grind)
    | exact resolve eq201598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201598
  have eq204497 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq203946 X1 X0
       grind)
    | exact superpose eq203946 eq11
    | (have j1 := eq203946 X1 X0
       grind)
    | exact resolve eq11 eq203946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203946
  have eq204811 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq35065
       have i₂ := eq204497 x X0
       grind)
    | exact superpose eq204497 eq35065
    | (have j1 := eq204497 x X0
       grind)
    | (have r₁ := eq35065
       have r₂ := eq204497 x x
       grind)
    | exact resolve eq35065 eq204497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204497
  have eq205044 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq204811 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204811
  have eq205306 : ∀ X0 : G, x = (M.op X0 x) ∨ (M.op x x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1875 X0 x
       have i₂ := eq205044 X0
       grind)
    | exact superpose eq205044 eq1875
    | (have j0 := eq1875 X0 x
       grind)
    | exact resolve eq1875 eq205044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq205460 : x = (M.op x x) := by
    first
    | (have i₁ := eq724 x
       have i₂ := eq205044 (M.op x x)
       grind)
    | exact superpose eq205044 eq724
    | exact resolve eq724 eq205044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq205524 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 x
       have i₂ := eq205044 (τ X0)
       grind)
    | exact superpose eq205044 eq17
    | exact resolve eq17 eq205044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq205044
  have eq205570 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ (M.op x x)) ≠ (k (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq42580 X0
       have i₂ := eq205524 X0
       grind)
    | exact superpose eq205524 eq42580
    | (have j0 := eq42580 X0
       grind)
    | exact resolve eq42580 eq205524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42580
  have eq205622 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ x)) ≠ (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq36883 X0
       have i₂ := eq205524 (M.op (σ x) (M.op X0 (σ x)))
       grind)
    | exact superpose eq205524 eq36883
    | (have j0 := eq36883 X0
       grind)
    | exact resolve eq36883 eq205524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36883
  have eq205635 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35065
       have i₂ := eq205460
       grind)
    | exact superpose eq205460 eq35065
    | exact resolve eq35065 eq205460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35065
  have eq205689 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq205306 X0
       have i₂ := eq205460
       grind)
    | exact superpose eq205460 eq205306
    | (have j0 := eq205306 X0
       grind)
    | exact resolve eq205306 eq205460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205306
  have eq205690 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq205689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205689
  have eq205731 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq205622 X0
       have i₂ := eq205460
       grind)
    | exact superpose eq205460 eq205622
    | exact resolve eq205622 eq205460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205460 eq205622
  have eq205755 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq205570 X0
       have i₂ := eq205524 (M.op X0 X0)
       grind)
    | exact superpose eq205524 eq205570
    | (have j0 := eq205570 X0
       grind)
    | exact resolve eq205570 eq205524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205524 eq205570
  have eq205806 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq205731 X0
       grind)
    | (have r₁ := eq205731 X0
       have r₂ := eq205635
       grind)
    | exact resolve eq205731 eq205635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205635 eq205731
  have eq205814 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq205755 X0
       have i₂ := eq205690 x
       grind)
    | exact superpose eq205690 eq205755
    | (have j0 := eq205755 X0
       grind)
    | exact resolve eq205755 eq205690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205690 eq205755
  have eq205815 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq205814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205814
  have eq205826 : False := by grind
  exact eq205826

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 X0)
       have i₂ := eq54 X0 X2
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq62
    | exact resolve eq62 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq347 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq346 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq346
    | (have j0 := eq346 (σ X0) (σ X1)
       grind)
    | exact resolve eq346 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq346 (τ X0) X1
       grind)
    | exact superpose eq346 eq17
    | (have j1 := eq346 (τ X0) X1
       grind)
    | exact resolve eq17 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq388 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq60 X1 X1 X0
       grind)
    | exact superpose eq60 eq62
    | exact resolve eq62 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq347 x y
       grind)
    | exact superpose eq347 eq16
    | (have j1 := eq347 x y
       grind)
    | exact resolve eq16 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq347 X0 X0
       grind)
    | exact superpose eq347 eq9
    | (have j1 := eq347 X0 X0
       grind)
    | exact resolve eq9 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq347 X0 X0
       grind)
    | exact superpose eq347 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq347 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq347 X0 X0
       grind)
    | exact resolve eq12 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (M.op X1 (M.op (σ (k X0 X0)) X2)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ X1) X1 X2
       have i₂ := eq347 X1 X1
       grind)
    | exact superpose eq347 eq62
    | (have j1 := eq347 X0 X0
       grind)
    | exact resolve eq62 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq455 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq347 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq456 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq449 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq449 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq449 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq468 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq455 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq455
    | (have j0 := eq455 (τ X0)
       grind)
    | exact resolve eq455 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq477 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq468 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq468
    | (have j0 := eq468 X0
       grind)
    | exact resolve eq468 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq484 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq477 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq477
    | (have j0 := eq477 X0
       grind)
    | exact resolve eq477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq511 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq87
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60 X2 X3 X1
       have i₂ := eq87 X1 X2 X0
       grind)
    | (have i₁ := eq60 X1 X1 X1
       have i₂ := eq87 X1 X1 X1
       grind)
    | exact superpose eq87 eq60
    | exact resolve eq60 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq639 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 (M.op X0 X1) X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq511
    | exact resolve eq511 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq678 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq639 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq639
    | exact resolve eq639 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq678 X2 X1
       have i₂ := eq87 X1 X2 X0
       grind)
    | (have i₁ := eq678 X1 X1
       have i₂ := eq87 X1 X1 X1
       grind)
    | exact superpose eq87 eq678
    | exact resolve eq678 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1562 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq456 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq456
    | (have j0 := eq456 (τ X0) X1
       grind)
    | exact resolve eq456 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1572 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1562 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1562
    | (have j0 := eq1562 X0 X1
       grind)
    | exact resolve eq1562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq1579 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1572 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1572
    | (have j0 := eq1572 X0 X1
       grind)
    | exact resolve eq1572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1975 : ∀ X0 X1 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X4 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq51 (M.op X0 X1) X1 (M.op X3 x) (M.op X1 x)
       have i₂ := eq520 X0 X1 x X3
       grind)
    | exact superpose eq520 eq51
    | exact resolve eq51 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq520
  have eq2023 : ∀ X0 X1 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X4 (M.op X3 X0)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1975 X0 X1 X3 X4
       have i₂ := eq678 X1 X0
       grind)
    | exact superpose eq678 eq1975
    | exact resolve eq1975 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq1975
  have eq2269 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq365 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq52 (τ X0)
       grind)
    | exact superpose eq52 eq365
    | (have j0 := eq365 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact resolve eq365 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq2292 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2269 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2269
    | (have j0 := eq2269 X0
       grind)
    | exact resolve eq2269 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2294 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2292 X0
       have i₂ := eq88 (τ X0) (τ X0)
       grind)
    | exact superpose eq88 eq2292
    | (have j0 := eq2292 X0
       grind)
    | exact resolve eq2292 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq2292
  have eq2597 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq440
       have i₂ := eq346 x y
       grind)
    | exact superpose eq346 eq440
    | (have j1 := eq346 (σ x) (σ y)
       grind)
    | exact resolve eq440 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq440
  have eq2600 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq2597
  have eq2603 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ x)
       have i₂ := eq2600
       grind)
    | exact superpose eq2600 eq9
    | exact resolve eq9 eq2600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5854 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op X1 (M.op (σ (τ X0)) X2)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq448 (τ X0) X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq448
    | (have j0 := eq448 (τ X0) X1 X2
       grind)
    | exact resolve eq448 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq448
  have eq5945 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5854 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5854
    | (have j0 := eq5854 X0 X1 X2
       grind)
    | exact resolve eq5854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5854
  have eq5956 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5945 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5945
    | (have j0 := eq5945 X0 X1 X2
       grind)
    | exact resolve eq5945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5945
  have eq8499 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5956 X0 x (k X0 X0)
       have i₂ := eq388 X0 (k X0 X0) x
       grind)
    | exact superpose eq388 eq5956
    | (have j0 := eq5956 X0 x x
       grind)
    | exact resolve eq5956 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq12112 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq2294 (σ X0)
       grind)
    | exact superpose eq2294 eq28
    | (have j1 := eq2294 (σ X0)
       grind)
    | exact resolve eq28 eq2294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294
  have eq12129 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12112 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq12112
    | (have j0 := eq12112 X0
       grind)
    | exact resolve eq12112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12112
  have eq12139 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12129 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12129
    | (have j0 := eq12129 X0
       grind)
    | exact resolve eq12129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12129
  have eq12146 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12139 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12139
    | (have j0 := eq12139 X0
       grind)
    | exact resolve eq12139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12139
  have eq12154 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12146 (M.op X0 X0)
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq12146
    | (have j0 := eq12146 X0
       grind)
    | exact resolve eq12146 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12146
  have eq12305 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12154 (k X0 X0)
       have i₂ := eq8499 X0
       grind)
    | exact superpose eq8499 eq12154
    | (have j0 := eq12154 X0
       have j1 := eq8499 X0
       grind)
    | exact resolve eq12154 eq8499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8499 eq12154
  have eq12326 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12305 X0
       have j1 := eq484 X0
       grind)
    | (have r₁ := eq12305 X0
       have r₂ := eq484 X0
       grind)
    | exact resolve eq12305 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq12305
  have eq12345 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12326 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq12326
    | (have j0 := eq12326 (τ X0)
       grind)
    | exact resolve eq12326 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12326
  have eq12385 : ∀ X0 : G, (τ X0) = (τ (k X0 (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12345 X0
       have i₂ := eq31 (k X0 X0) X0
       grind)
    | exact superpose eq31 eq12345
    | (have j0 := eq12345 X0
       grind)
    | exact resolve eq12345 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq12345
  have eq116353 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2603 (σ y)
       have i₂ := eq2600
       grind)
    | exact superpose eq2600 eq2603
    | exact resolve eq2603 eq2600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq116653 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op y x) := by grind
  clear eq116353
  have eq116908 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq639 (σ x) (M.op (σ y) (σ y))
       have i₂ := eq116653
       grind)
    | exact superpose eq116653 eq639
    | exact resolve eq639 eq116653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116653
  have eq117164 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2600
       have i₂ := eq116908
       grind)
    | exact superpose eq116908 eq2600
    | exact resolve eq2600 eq116908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116908
  have eq117348 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq117164
  have eq117412 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq85 (σ x) x
       have i₂ := eq117348
       grind)
    | exact superpose eq117348 eq85
    | (have r₁ := eq85 (σ x) x
       have r₂ := eq117348
       grind)
    | exact resolve eq85 eq117348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117604 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq117412 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117412
  have eq117680 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq117604 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq117604
    | exact resolve eq117604 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117604
  have eq118758 : (σ x) = (σ (k x x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq117348
       have i₂ := eq117680 x
       grind)
    | exact superpose eq117680 eq117348
    | exact resolve eq117348 eq117680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117348
  have eq118761 : (σ x) = (σ (k y x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2600
       have i₂ := eq117680 y
       grind)
    | exact superpose eq117680 eq2600
    | exact resolve eq2600 eq117680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600 eq117680
  have eq119025 : (σ x) = (σ (k y x)) ∨ x = (M.op y x) := by grind
  clear eq118761
  have eq119028 : (σ x) = (σ (k x x)) ∨ x = (M.op y x) := by grind
  clear eq118758
  have eq119139 : (k y x) = (τ (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq119025
       grind)
    | exact superpose eq119025 eq10
    | exact resolve eq10 eq119025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119025
  have eq119252 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq119139
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq119139
    | exact resolve eq119139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119139
  have eq119951 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq119028
       grind)
    | exact superpose eq119028 eq10
    | exact resolve eq10 eq119028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119028
  have eq120072 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq119951
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq119951
    | exact resolve eq119951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119951
  have eq120084 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1579 x X0
       have i₂ := eq120072
       grind)
    | exact superpose eq120072 eq1579
    | (have j0 := eq1579 x X0
       grind)
    | (have r₁ := eq1579 x x
       have r₂ := eq120072
       grind)
    | exact resolve eq1579 eq120072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579 eq120072
  have eq120197 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq120084 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120084
  have eq121515 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq119252
       have i₂ := eq120197 y
       grind)
    | exact superpose eq120197 eq119252
    | exact resolve eq119252 eq120197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119252 eq120197
  have eq121518 : x = (M.op y x) := by grind
  clear eq121515
  have eq121552 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq639 y x
       have i₂ := eq121518
       grind)
    | exact superpose eq121518 eq639
    | exact resolve eq639 eq121518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121556 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq985 y x X0
       have i₂ := eq121518
       grind)
    | exact superpose eq121518 eq985
    | exact resolve eq985 eq121518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq121596 : ∀ X0 : G, y = (M.op (M.op X0 x) (k y y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq5956 y X0 x
       have i₂ := eq121518
       grind)
    | exact superpose eq121518 eq5956
    | (have j0 := eq5956 y x x
       grind)
    | exact resolve eq5956 eq121518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5956
  have eq121714 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq121552
       grind)
    | exact superpose eq121552 eq12
    | (have j0 := eq12 X0 y
       grind)
    | exact resolve eq12 eq121552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121715 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq121552
       grind)
    | exact superpose eq121552 eq52
    | exact resolve eq52 eq121552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125084 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq121556 y
       have i₂ := eq121715
       grind)
    | exact superpose eq121715 eq121556
    | exact resolve eq121556 eq121715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121556 eq121715
  have eq125920 : (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq639 x (M.op x y)
       have i₂ := eq125084
       grind)
    | exact superpose eq125084 eq639
    | exact resolve eq639 eq125084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125084
  have eq126131 : x = (M.op x x) := by
    first
    | (have i₁ := eq125920
       have i₂ := eq121518
       grind)
    | exact superpose eq121518 eq125920
    | exact resolve eq125920 eq121518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125920
  have eq126245 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq85 x x
       have i₂ := eq126131
       grind)
    | exact superpose eq126131 eq85
    | (have r₁ := eq85 x x
       have r₂ := eq126131
       grind)
    | exact resolve eq85 eq126131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126436 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq126245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126245
  have eq126518 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq456 x X0
       have i₂ := eq126436 x
       grind)
    | exact superpose eq126436 eq456
    | (have j0 := eq456 x X0
       grind)
    | exact resolve eq456 eq126436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq126733 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq126518 X0
       have i₂ := eq126131
       grind)
    | exact superpose eq126131 eq126518
    | (have j0 := eq126518 X0
       grind)
    | exact resolve eq126518 eq126131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126131 eq126518
  have eq126734 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq126733 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126733
  have eq132466 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq126734 (σ X0)
       grind)
    | exact superpose eq126734 eq15
    | exact resolve eq15 eq126734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126734
  have eq132537 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq132466 X0
       have i₂ := eq126436 X0
       grind)
    | exact superpose eq126436 eq132466
    | exact resolve eq132466 eq126436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126436 eq132466
  have eq135296 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq639 (σ X0) (σ x)
       have i₂ := eq132537 X0
       grind)
    | exact superpose eq132537 eq639
    | exact resolve eq639 eq132537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132537
  have eq219638 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq135296 y
       have i₂ := eq121518
       grind)
    | exact superpose eq121518 eq135296
    | exact resolve eq135296 eq121518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121518 eq135296
  have eq220111 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52 (σ y)
       have i₂ := eq219638
       grind)
    | exact superpose eq219638 eq52
    | exact resolve eq52 eq219638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq220696 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2023 (σ x) (σ y) X1 X0
       have i₂ := eq220111
       grind)
    | exact superpose eq220111 eq2023
    | exact resolve eq2023 eq220111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023 eq220111
  have eq275226 : ∀ X0 : G, y = (M.op (M.op X0 x) (k y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq121596 X0
       have i₂ := eq121552
       grind)
    | exact superpose eq121552 eq121596
    | (have j0 := eq121596 X0
       grind)
    | exact resolve eq121596 eq121552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121596
  have eq275315 : y = (M.op (k y y) (k y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq275226 (k y y)
       have i₂ := eq639 (k y y) x
       grind)
    | exact superpose eq639 eq275226
    | exact resolve eq275226 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq275226
  have eq281623 : (k y y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq54 (k y y) (k y y)
       have i₂ := eq275315
       grind)
    | exact superpose eq275315 eq54
    | exact resolve eq54 eq275315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq275315
  have eq281842 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq121714 y
       grind)
    | (have r₁ := eq281623
       have r₂ := eq121714 x
       grind)
    | exact resolve eq281623 eq121714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121714 eq281623
  have eq281877 : (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq281842
       have i₂ := eq121552
       grind)
    | exact superpose eq121552 eq281842
    | exact resolve eq281842 eq121552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281842
  have eq665625 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq220696 x (σ (k y y))
       have i₂ := eq454 y x (σ x)
       grind)
    | exact superpose eq454 eq220696
    | (have j1 := eq454 y x x
       grind)
    | exact resolve eq220696 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq220696
  have eq666248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq665625
       have i₂ := eq281877
       grind)
    | exact superpose eq281877 eq665625
    | exact resolve eq665625 eq281877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665625
  have eq666369 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq666248
       have r₂ := eq16
       grind)
    | exact resolve eq666248 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666248
  have eq666433 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq666369
       have i₂ := eq219638
       grind)
    | exact superpose eq219638 eq666369
    | exact resolve eq666369 eq219638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666494 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq85 (σ y) x
       have i₂ := eq666369
       grind)
    | exact superpose eq666369 eq85
    | (have r₁ := eq85 (σ y) x
       have r₂ := eq666369
       grind)
    | exact resolve eq85 eq666369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq666369
  have eq666813 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq666494 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666494
  have eq666932 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq666433
       grind)
    | exact superpose eq666433 eq16
    | exact resolve eq16 eq666433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667585 : (τ (σ y)) = (τ (k (σ y) (M.op (σ y) (σ y)))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq12385 (σ y)
       have i₂ := eq666813 (σ y)
       grind)
    | exact superpose eq666813 eq12385
    | (have j0 := eq12385 (σ y)
       grind)
    | exact resolve eq12385 eq666813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12385 eq666813
  have eq667958 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq667585
       have i₂ := eq28 y (M.op (σ y) (σ y))
       grind)
    | exact superpose eq28 eq667585
    | exact resolve eq667585 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq667585
  have eq668034 : (τ (σ y)) = (k y (τ (M.op (σ x) (σ y)))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq667958
       have i₂ := eq219638
       grind)
    | exact superpose eq219638 eq667958
    | exact resolve eq667958 eq219638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219638 eq667958
  have eq668102 : (τ (σ y)) = (k y (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq668034
       have i₂ := eq666433
       grind)
    | exact superpose eq666433 eq668034
    | exact resolve eq668034 eq666433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666433 eq668034
  have eq668140 : y = (k y y) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq668102
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq668102
    | exact resolve eq668102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668102
  have eq668166 : y = (M.op x y) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq668140
       have i₂ := eq281877
       grind)
    | exact superpose eq281877 eq668140
    | exact resolve eq668140 eq281877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281877 eq668140
  have eq668183 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq668166
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq668166
    | exact resolve eq668166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668166
  have eq668190 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq668183
       have i₂ := eq121552
       grind)
    | exact superpose eq121552 eq668183
    | exact resolve eq668183 eq121552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121552 eq668183
  have eq668191 : y = (M.op x y) := by grind
  clear eq668190
  have eq669484 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq666932
       have i₂ := eq668191
       grind)
    | exact superpose eq668191 eq666932
    | exact resolve eq666932 eq668191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666932 eq668191
  have eq669787 : False := by grind
  exact eq669787

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
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
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq45
    | (have j0 := eq45 (M.op x y)
       grind)
    | exact resolve eq45 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq180 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq180
    | (have j0 := eq180 y x
       grind)
    | exact resolve eq180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ y) (σ x)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0)
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 (k X0 X0) X0
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (k X0 X1)) (M.op X0 X0)) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : (M.op x y) = (k x y) ∨ y = (M.op y x) := by
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
  have eq625 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq630 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq601 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq601 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq601 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq633 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq620
       grind)
    | exact superpose eq620 eq41
    | exact resolve eq41 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq633
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq633
    | exact resolve eq633 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq636 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq634
    | exact resolve eq634 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq636 eq625
    | exact resolve eq625 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq653 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq646
       have r₂ := eq27
       grind)
    | exact resolve eq646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq659 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq653 eq180
    | exact resolve eq180 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq178 X0
       grind)
    | exact resolve eq12 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq28 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq653 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq653
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq653
       grind)
    | exact resolve eq12 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq682
  have eq687 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq669 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq690 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq636 eq685
    | exact resolve eq685 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq699 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq687 X0
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq687
    | (have j0 := eq687 X0
       grind)
    | exact resolve eq687 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq701 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq699
    | (have j0 := eq699 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq699 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq702 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq631 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq631
    | (have j0 := eq631 (σ X0) X1
       grind)
    | exact resolve eq631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq690 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq690
       grind)
    | exact resolve eq13 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq741 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq810 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq741 eq26
    | (have j1 := eq741 (σ x)
       grind)
    | exact resolve eq26 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq636 eq810
    | exact resolve eq810 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq810
  have eq838 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq823
       have r₂ := eq27
       grind)
    | exact resolve eq823 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq843 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq838
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq838
    | (have j1 := eq28 (σ x) (σ x)
       grind)
    | exact resolve eq838 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq838 eq659
    | exact resolve eq659 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq855 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq838 eq180
    | exact resolve eq180 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq844
  have eq889 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq855 eq16
    | exact resolve eq16 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq995 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq653 eq889
    | exact resolve eq889 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq1007 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq995
  have eq1014 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq653 eq1007
    | exact resolve eq1007 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq1007
  have eq1016 : y ≠ y ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1014
       grind)
    | exact superpose eq1014 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1014
       grind)
    | exact resolve eq12 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : x = (M.op y (M.op x x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq180 x y
       have i₂ := eq1014
       grind)
    | exact superpose eq1014 eq180
    | exact resolve eq180 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : (k x y) = (M.op x x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1016
  have eq1465 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq843 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq843
       grind)
    | exact resolve eq13 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1469 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1465 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1481 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1014 eq1469
    | (have j0 := eq1469 X0
       grind)
    | exact resolve eq1469 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1612 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ (k X0 X1))) (M.op (σ X0) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq604 (σ X0) (σ X1) X2
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq604
    | (have j0 := eq604 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1919 : x = (M.op y (k x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1018
       have i₂ := eq1020
       grind)
    | exact superpose eq1020 eq1018
    | exact resolve eq1018 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1924 : x = (M.op x (k x y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq1020
       grind)
    | exact superpose eq1020 eq178
    | exact resolve eq178 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1934 : x = (M.op (k x y) (k x y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq180 x x
       have i₂ := eq1020
       grind)
    | exact superpose eq1020 eq180
    | exact resolve eq180 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1937 : x = (M.op y (k x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq1919
  have eq2598 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq177 X1 X4 X0 X2
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq3204 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1481 eq838
    | exact resolve eq838 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq1481
  have eq3221 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq3204
  have eq3265 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1014 eq3221
    | exact resolve eq3221 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221
  have eq3266 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq3265
  have eq3307 : (τ (σ y)) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3266 eq98
    | exact resolve eq98 eq3266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3325 : y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq3307
    | exact resolve eq3307 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3307
  have eq4619 : x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq600 x
       have i₂ := eq3325
       grind)
    | exact superpose eq3325 eq600
    | (have j0 := eq600 x
       grind)
    | exact resolve eq600 eq3325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3325
  have eq4629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3266 eq600
    | (have j0 := eq600 (σ x)
       grind)
    | exact resolve eq600 eq3266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4654 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq4629
    | exact resolve eq4629 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4629
  have eq4659 : y = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4619
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4619
    | exact resolve eq4619 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4619
  have eq4682 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq4654 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq4654
       grind)
    | exact resolve eq13 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654
  have eq4698 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq4682 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq4729 : y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq4659
       grind)
    | exact superpose eq4659 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq4659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4739 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4729
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4729
    | exact resolve eq4729 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4729
  have eq4740 : y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq4739
  have eq4745 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq4740
       grind)
    | exact superpose eq4740 eq40
    | exact resolve eq40 eq4740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4740
  have eq4751 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4745
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4745
    | exact resolve eq4745 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4745
  have eq5004 : (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4698 eq178
    | exact resolve eq178 eq4698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4698
  have eq5141 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3266 eq5004
    | exact resolve eq5004 eq3266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3266 eq5004
  have eq5177 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq5141
    | exact resolve eq5141 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5141
  have eq5178 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5177
  have eq5207 : y ≠ y ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq5178
       grind)
    | exact superpose eq5178 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq5178
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq5178
       grind)
    | exact resolve eq12 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5212 : x = (M.op y (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 x y
       have i₂ := eq5178
       grind)
    | exact superpose eq5178 eq180
    | exact resolve eq180 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5217 : (k x y) = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5207
  have eq5543 : x = (M.op y (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5212
       have i₂ := eq5217
       grind)
    | exact superpose eq5217 eq5212
    | exact resolve eq5212 eq5217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5212
  have eq5550 : x = (M.op x (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq5217
       grind)
    | exact superpose eq5217 eq178
    | exact resolve eq178 eq5217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5562 : x = (M.op (k x y) (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 x x
       have i₂ := eq5217
       grind)
    | exact superpose eq5217 eq180
    | exact resolve eq180 eq5217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5569 : x = (M.op y (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq5543
  have eq6975 : ∀ X0 : G, (k x y) = (M.op (M.op X0 x) x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 (k x y) x (k x y)
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq16
    | exact resolve eq16 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934
  have eq8972 : (k x y) = (M.op y x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6975 y
       have i₂ := eq1014
       grind)
    | exact superpose eq1014 eq6975
    | exact resolve eq6975 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6975
  have eq9010 : (k x y) = (M.op y x) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq8972
  have eq9037 : y = (k x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1014 eq9010
    | exact resolve eq9010 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq9010
  have eq9043 : x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1924
       have i₂ := eq9037
       grind)
    | exact superpose eq9037 eq1924
    | exact resolve eq1924 eq9037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924
  have eq9047 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1937
       have i₂ := eq9037
       grind)
    | exact superpose eq9037 eq1937
    | exact resolve eq1937 eq9037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937 eq9037
  have eq9058 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq9047
  have eq9062 : x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9043
  have eq9067 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq9062
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9062
    | exact resolve eq9062 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9062
  have eq9071 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq190
       have i₂ := eq9067
       grind)
    | exact superpose eq9067 eq190
    | exact resolve eq190 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9084 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq9067
       grind)
    | exact superpose eq9067 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq9067
       grind)
    | exact resolve eq13 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9093 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 y x y
       have i₂ := eq9067
       grind)
    | exact superpose eq9067 eq16
    | exact resolve eq16 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9100 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq9084 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9084
  have eq9121 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9058
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq9058
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq9058 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9122 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq190
       have i₂ := eq9058
       grind)
    | exact superpose eq9058 eq190
    | exact resolve eq190 eq9058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9135 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq9058
       grind)
    | exact superpose eq9058 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq9058
       grind)
    | exact resolve eq13 eq9058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9144 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq16 y x y
       have i₂ := eq9058
       grind)
    | exact superpose eq9058 eq16
    | exact resolve eq16 eq9058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9058
  have eq9152 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq9135 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9135
  have eq9160 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq9093 eq9144
    | (have j0 := eq9144 X0
       have j1 := eq9093 X0
       grind)
    | exact resolve eq9144 eq9093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9093 eq9144
  have eq9167 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq9100 eq9152
    | (have j0 := eq9152 X0
       have j1 := eq9100 X0
       grind)
    | exact resolve eq9152 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9152
  have eq9178 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq9071 eq9122
    | exact resolve eq9122 eq9071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9071 eq9122
  have eq9179 : (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq630 y
       grind)
    | (have r₁ := eq9121
       have r₂ := eq630 y
       grind)
    | exact resolve eq9121 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9121
  have eq9184 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq9067 eq9179
    | exact resolve eq9179 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9179
  have eq9301 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9100 x
       grind)
    | exact superpose eq9100 eq18
    | (have j1 := eq9100 x
       grind)
    | exact resolve eq18 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9314 : y = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq9067
       have i₂ := eq9100 y
       grind)
    | exact superpose eq9100 eq9067
    | exact resolve eq9067 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9067 eq9100
  have eq9324 : y = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9314
  have eq9378 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq9301
       grind)
    | exact superpose eq9301 eq41
    | exact resolve eq41 eq9301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9301
  have eq9390 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq9378
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9378
    | exact resolve eq9378 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9378
  have eq9392 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq9390
    | exact resolve eq9390 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9390
  have eq9405 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq9324
       grind)
    | exact superpose eq9324 eq41
    | exact resolve eq41 eq9324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9324
  have eq9420 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq9405
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9405
    | exact resolve eq9405 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9405
  have eq9482 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq9420 eq631
    | (have j0 := eq631 (σ y) X0
       grind)
    | (have r₁ := eq631 (σ y) x
       have r₂ := eq9420
       grind)
    | exact resolve eq631 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9420
  have eq9489 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq9482 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9482
  have eq9673 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq9178
       grind)
    | exact superpose eq9178 eq178
    | exact resolve eq178 eq9178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9674 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq180 y X0
       have i₂ := eq9178
       grind)
    | exact superpose eq9178 eq180
    | exact resolve eq180 eq9178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9178
  have eq9716 : y = (k (M.op x y) y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq701 y
       have i₂ := eq9184
       grind)
    | exact superpose eq9184 eq701
    | (have j0 := eq701 y
       grind)
    | exact resolve eq701 eq9184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9717 : y = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq600 y
       have i₂ := eq9184
       grind)
    | exact superpose eq9184 eq600
    | (have j0 := eq600 y
       grind)
    | exact resolve eq600 eq9184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9184
  have eq9727 : y = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9717
  have eq9728 : y = (k (M.op x y) y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9716
  have eq9955 : y = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq9673 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq9673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9673
  have eq9963 : y = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9955
  have eq10029 : y ≠ y ∨ y = (M.op y y) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9727 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | (have r₁ := eq12 (M.op x y) y
       have r₂ := eq9727
       grind)
    | (have r₁ := eq12 y y
       have r₂ := eq9727
       grind)
    | exact resolve eq12 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9727
  have eq10040 : y ≠ y ∨ y = (M.op y y) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10029
  have eq10041 : y = (M.op y y) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10040
  have eq10045 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9728 eq10041
    | exact resolve eq10041 eq9728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9728 eq10041
  have eq10116 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9963 eq38
    | exact resolve eq38 eq9963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq9963
  have eq10128 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq10116
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10116
    | exact resolve eq10116 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10116
  have eq10190 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10045 eq180
    | exact resolve eq180 eq10045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10045
  have eq10277 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9489 eq26
    | (have j1 := eq9489 (σ x)
       grind)
    | exact resolve eq26 eq9489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9489
  have eq10301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9392 eq10277
    | exact resolve eq10277 eq9392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9392 eq10277
  have eq10317 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10301
       have r₂ := eq27
       grind)
    | exact resolve eq10301 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10301
  have eq10325 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10317 eq29
    | exact resolve eq29 eq10317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10330 : (k x (M.op x y)) = (τ (k (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10317 eq100
    | exact resolve eq100 eq10317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq10347 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10317 eq858
    | exact resolve eq858 eq10317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq10370 : (k x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99 eq10330
    | exact resolve eq10330 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq10330
  have eq10375 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq10325
    | exact resolve eq10325 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10325
  have eq10379 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10375
       grind)
    | exact superpose eq10375 eq18
    | exact resolve eq18 eq10375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10385 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq620
       have i₂ := eq10375
       grind)
    | exact superpose eq10375 eq620
    | exact resolve eq620 eq10375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq10421 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4659
       have i₂ := eq10375
       grind)
    | exact superpose eq10375 eq4659
    | exact resolve eq4659 eq10375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10499 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq10421
  have eq10517 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10379 eq175
    | exact resolve eq175 eq10379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq10678 : ∀ X0 : G, x = (M.op (M.op X0 (k x (M.op x y))) (M.op x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq604 x y X0
       have i₂ := eq10370
       grind)
    | exact superpose eq10370 eq604
    | (have j0 := eq604 x (M.op x y) X0
       grind)
    | exact resolve eq604 eq10370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10370
  have eq10683 : ∀ X0 : G, x = (M.op (M.op X0 (k x (M.op x y))) x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4659 eq10678
    | exact resolve eq10678 eq4659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4659 eq10678
  have eq10691 : ∀ X0 : G, x = (M.op (M.op X0 (k x (M.op x y))) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10375 eq10683
    | (have j0 := eq10683 X0
       grind)
    | exact resolve eq10683 eq10375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10683
  have eq10696 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10385 eq10691
    | exact resolve eq10691 eq10385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10385 eq10691
  have eq11623 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10347 eq180
    | exact resolve eq180 eq10347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10347
  have eq11654 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10375 eq11623
    | exact resolve eq11623 eq10375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11623
  have eq11879 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11654 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq11654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11654
  have eq12696 : ∀ X0 : G, y = (k (M.op X0 y) y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9160 X0
       have i₂ := eq9167 (M.op X0 y)
       grind)
    | exact superpose eq9167 eq9160
    | exact resolve eq9160 eq9167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9160
  have eq12704 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9167 x
       grind)
    | exact superpose eq9167 eq18
    | (have j1 := eq9167 x
       grind)
    | exact resolve eq18 eq9167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12720 : (M.op x y) = (k y y) ∨ y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10190
       have i₂ := eq9167 y
       grind)
    | exact superpose eq9167 eq10190
    | exact resolve eq10190 eq9167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10190
  have eq12733 : (M.op x y) ≠ (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  have eq12739 : (M.op x y) = (k y y) ∨ y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq12720
  have eq12750 : ∀ X0 : G, y = (k (M.op X0 y) y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq12696 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12696
  have eq12771 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y y) := by
    first
    | (have r₁ := eq12739
       have r₂ := eq12733
       grind)
    | exact resolve eq12739 eq12733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12733 eq12739
  have eq12782 : (M.op x y) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq10317 eq12704
    | exact resolve eq12704 eq10317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12704
  have eq12785 : ∀ X0 : G, y = (k (k X0 y) y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq9167 eq12750
    | exact resolve eq12750 eq9167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9167 eq12750
  have eq12840 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq12782 eq41
    | exact resolve eq41 eq12782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12853 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq12840
    | exact resolve eq12840 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12840
  have eq12864 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq12853 eq10128
    | exact resolve eq10128 eq12853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10128 eq12853
  have eq12883 : (M.op x y) = (M.op y y) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12864
  have eq12930 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq180 y y
       have i₂ := eq12771
       grind)
    | exact superpose eq12771 eq180
    | exact resolve eq180 eq12771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12771
  have eq12989 : y = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq12883
       grind)
    | exact superpose eq12883 eq178
    | exact resolve eq178 eq12883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12883
  have eq13006 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12989
  have eq13034 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13006 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq13006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13006
  have eq13229 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq631 y X0
       have i₂ := eq12930
       grind)
    | exact superpose eq12930 eq631
    | (have j0 := eq631 y X0
       grind)
    | (have r₁ := eq631 y x
       have r₂ := eq12930
       grind)
    | exact resolve eq631 eq12930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq12930
  have eq13236 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq13229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13229
  have eq13753 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13034 eq9674
    | (have j0 := eq9674 x
       grind)
    | exact resolve eq9674 eq13034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9674
  have eq13778 : y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13753
  have eq14111 : y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq12782 eq12785
    | exact resolve eq12785 eq12782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12785
  have eq14132 : y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq14111
  have eq14146 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12782 eq14132
    | exact resolve eq14132 eq12782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12782 eq14132
  have eq14188 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq180 y y
       have i₂ := eq14146
       grind)
    | exact superpose eq14146 eq180
    | exact resolve eq180 eq14146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14146
  have eq17450 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10379 eq10696
    | exact resolve eq10696 eq10379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10696
  have eq17493 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq17450
  have eq17519 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17493 eq28
    | (have j0 := eq28 (M.op x y) x
       grind)
    | exact resolve eq28 eq17493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17493
  have eq17534 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10379 eq17519
    | exact resolve eq17519 eq10379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17519
  have eq17535 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq17534
  have eq17539 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq17535 eq40
    | exact resolve eq40 eq17535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq17535
  have eq17544 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq17539
    | exact resolve eq17539 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17539
  have eq17546 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq10317 eq17544
    | exact resolve eq17544 eq10317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17544
  have eq17832 : (M.op x y) = (k (M.op x y) y) ∨ y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq13034
       have i₂ := eq13236 sF0
       grind)
    | exact superpose eq13236 eq13034
    | exact resolve eq13034 eq13236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13034 eq13236
  have eq17845 : (M.op x y) = (k (M.op x y) y) ∨ y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq17832
  have eq17933 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13778 eq17845
    | exact resolve eq17845 eq13778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13778 eq17845
  have eq17974 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq14188 eq17933
    | exact resolve eq17933 eq14188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17933
  have eq17975 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq17974
  have eq18036 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq17975 eq670
    | (have j0 := eq670 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq670 (M.op x y) (M.op x y)
       have r₂ := eq17975
       grind)
    | exact resolve eq670 eq17975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq17975
  have eq18038 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq18036
  have eq18039 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq18038
  have eq18053 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq18039
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq18039
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq18039 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18109 : y ≠ (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq18039
  have eq18142 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq18109
       have r₂ := eq14188
       grind)
    | exact resolve eq18109 eq14188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14188 eq18109
  have eq18156 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq630 (M.op x y)
       grind)
    | (have r₁ := eq18053
       have r₂ := eq630 (M.op x y)
       grind)
    | exact resolve eq18053 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18053
  have eq19492 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq18156 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq18156
       grind)
    | exact resolve eq13 eq18156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18156
  have eq19508 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq19492 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19492
  have eq20704 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19508 eq18142
    | exact resolve eq18142 eq19508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18142 eq19508
  have eq20719 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20704
  have eq20807 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20719 eq42
    | exact resolve eq42 eq20719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20719
  have eq20820 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq20807
    | exact resolve eq20807 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20807
  have eq20822 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20820
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20820
    | exact resolve eq20820 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20820
  have eq20835 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20822 eq701
    | (have j0 := eq701 (σ (M.op x y))
       grind)
    | exact resolve eq701 eq20822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq20836 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20822 eq600
    | (have j0 := eq600 (σ (M.op x y))
       grind)
    | exact resolve eq600 eq20822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21141 : (τ (σ (M.op x y))) = (k y (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20835 eq108
    | exact resolve eq108 eq20835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq21148 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq21141
    | exact resolve eq21141 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21141
  have eq21171 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20836 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq20836
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq20836
       grind)
    | exact resolve eq12 eq20836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20836
  have eq21182 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq21171
  have eq21183 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq21182
  have eq21188 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20835 eq21183
    | exact resolve eq21183 eq20835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20835 eq21183
  have eq21209 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq21148 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq21148
       grind)
    | exact resolve eq13 eq21148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21225 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq21209 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21209
  have eq21279 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21188 eq28
    | (have j0 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq28 eq21188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21188
  have eq21288 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq21279
  have eq21379 : (τ (σ (M.op x y))) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21288 eq116
    | exact resolve eq116 eq21288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq21288
  have eq21420 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq29 eq21379
    | exact resolve eq21379 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21379
  have eq21456 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y y) := by
    intro X0
    first
    | exact superpose eq21420 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq21420
       grind)
    | exact resolve eq13 eq21420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21472 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y y) := by
    intro X0
    first
    | (have j0 := eq21456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21456
  have eq22128 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21225 eq21148
    | exact resolve eq21148 eq21225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21148 eq21225
  have eq22144 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22128
  have eq22162 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20822 eq22144
    | exact resolve eq22144 eq20822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22144
  have eq22163 : (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22162
  have eq22192 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22163 eq37
    | exact resolve eq37 eq22163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq22163
  have eq22202 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq22192
    | exact resolve eq22192 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22192
  have eq22902 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq21472 eq21420
    | exact resolve eq21420 eq21472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21420 eq21472
  have eq22922 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y y) := by grind
  clear eq22902
  have eq22949 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq20822 eq22922
    | exact resolve eq22922 eq20822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20822 eq22922
  have eq22950 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22949
  have eq22993 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq22950
       grind)
    | exact superpose eq22950 eq41
    | exact resolve eq41 eq22950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq22950
  have eq23031 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq22993
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22993
    | exact resolve eq22993 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22993
  have eq23035 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq23031
    | exact resolve eq23031 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23031
  have eq23063 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23035 eq600
    | (have j0 := eq600 (σ y)
       grind)
    | exact resolve eq600 eq23035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq23068 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq23035 eq604
    | (have j0 := eq604 (σ y) (σ y) x
       grind)
    | exact resolve eq604 eq23035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq23081 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq28 eq23068
    | (have j1 := eq28 (σ y) (σ y)
       grind)
    | exact resolve eq23068 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23068
  have eq23085 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq23035 eq23081
    | exact resolve eq23081 eq23035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23081
  have eq23235 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq23063 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq23063
       grind)
    | exact resolve eq13 eq23063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23251 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq23235 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23235
  have eq23860 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23085 eq194
    | exact resolve eq194 eq23085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23085
  have eq24307 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23251 eq23063
    | exact resolve eq23063 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23063 eq23251
  have eq24329 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq24307
  have eq24372 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23035 eq24329
    | exact resolve eq24329 eq23035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23035 eq24329
  have eq24373 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq24372
  have eq24417 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24373 eq28
    | (have j0 := eq28 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq28 eq24373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24373
  have eq24439 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22202 eq24417
    | exact resolve eq24417 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22202 eq24417
  have eq24440 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq24439
  have eq24474 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24440 eq180
    | exact resolve eq180 eq24440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24562 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23860 eq24474
    | exact resolve eq24474 eq23860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23860 eq24474
  have eq24593 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq24562
  have eq24602 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24440 eq24593
    | exact resolve eq24593 eq24440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24440 eq24593
  have eq24603 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq24602
  have eq24911 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq24603 eq16
    | exact resolve eq16 eq24603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24915 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24603 eq180
    | exact resolve eq180 eq24603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24603
  have eq34432 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 (M.op X1 (M.op x X2))) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2598 X0 x X2 x y
       have i₂ := eq5178
       grind)
    | exact superpose eq5178 eq2598
    | exact resolve eq2598 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35271 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34432 (M.op x (M.op x (M.op X0 x))) (M.op x X0) X0
       have i₂ := eq2598 x X0 x x x
       grind)
    | exact superpose eq2598 eq34432
    | exact resolve eq34432 eq2598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598 eq34432
  have eq35362 : y = (M.op x (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35271 (M.op x x)
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq35271
    | exact resolve eq35271 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35271
  have eq35475 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 (M.op y y)
       have i₂ := eq35362
       grind)
    | exact superpose eq35362 eq16
    | exact resolve eq16 eq35362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35645 : x = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35475 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35475
    | (have j0 := eq35475 x
       grind)
    | exact resolve eq35475 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35475
  have eq35715 : x = (M.op (M.op x y) (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35645
       have i₂ := eq5217
       grind)
    | exact superpose eq5217 eq35645
    | exact resolve eq35645 eq5217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5217 eq35645
  have eq35742 : x = (M.op (M.op x y) (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq35715
  have eq39298 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11879 eq98
    | exact resolve eq98 eq11879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq11879
  have eq39332 : y = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq39298
    | exact resolve eq39298 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq39298
  have eq39336 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10375 eq39332
    | exact resolve eq39332 eq10375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39332
  have eq49181 : ∀ X0 : G, (k x y) = (M.op (M.op X0 x) x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x y) x (k x y)
       have i₂ := eq5562
       grind)
    | exact superpose eq5562 eq16
    | exact resolve eq16 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5562
  have eq50539 : (k x y) = (M.op y x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49181 y
       have i₂ := eq5178
       grind)
    | exact superpose eq5178 eq49181
    | exact resolve eq49181 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49181
  have eq50607 : (k x y) = (M.op y x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50539
  have eq50644 : y = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5178 eq50607
    | exact resolve eq50607 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178 eq50607
  have eq50692 : x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5550
       have i₂ := eq50644
       grind)
    | exact superpose eq50644 eq5550
    | exact resolve eq5550 eq50644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5550
  have eq50696 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5569
       have i₂ := eq50644
       grind)
    | exact superpose eq50644 eq5569
    | exact resolve eq5569 eq50644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5569
  have eq50702 : x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35742
       have i₂ := eq50644
       grind)
    | exact superpose eq50644 eq35742
    | exact resolve eq35742 eq50644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35742 eq50644
  have eq50720 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) := by grind
  clear eq50702
  have eq50724 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq50696
  have eq50728 : x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50692
  have eq50742 : x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50728
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50728
    | exact resolve eq50728 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50728
  have eq50750 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10375 eq50742
    | exact resolve eq50742 eq10375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50742
  have eq50857 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq50750 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq50750
       grind)
    | exact resolve eq13 eq50750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50879 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq50857 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50857
  have eq50952 : y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq190
       have i₂ := eq50724
       grind)
    | exact superpose eq50724 eq190
    | exact resolve eq190 eq50724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50985 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq35362
       have i₂ := eq50724
       grind)
    | exact superpose eq50724 eq35362
    | exact resolve eq35362 eq50724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35362
  have eq51022 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq50724
       grind)
    | exact superpose eq50724 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq50724
       grind)
    | exact resolve eq13 eq50724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50724
  have eq51045 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq51022 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51022
  have eq51054 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq50985
  have eq51080 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51054
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51054
    | exact resolve eq51054 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq51054
  have eq51090 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10375 eq51080
    | exact resolve eq51080 eq10375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10375 eq51080
  have eq51173 : y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq51090
       grind)
    | exact superpose eq51090 eq178
    | exact resolve eq178 eq51090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq51176 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq194 y
       have i₂ := eq51090
       grind)
    | exact superpose eq51090 eq194
    | exact resolve eq194 eq51090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51187 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq180 y y
       have i₂ := eq51090
       grind)
    | exact superpose eq51090 eq180
    | exact resolve eq180 eq51090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51339 : y ≠ y ∨ y = (M.op y y) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51173 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | (have r₁ := eq12 (M.op x y) y
       have r₂ := eq51173
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq51173
       grind)
    | exact resolve eq12 eq51173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51173
  have eq51353 : y = (M.op y y) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq51339
  have eq51370 : y = (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51090 eq51353
    | exact resolve eq51353 eq51090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51353
  have eq51371 : y = (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51370
  have eq51379 : y = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51187 eq51371
    | exact resolve eq51371 eq51187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51371
  have eq51561 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51187 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq51187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51187
  have eq51574 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51561
  have eq54153 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50879 eq10379
    | exact resolve eq10379 eq50879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10379
  have eq54208 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50879 eq50750
    | exact resolve eq50750 eq50879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50879
  have eq54242 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq54208
  have eq54272 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq54153
  have eq54421 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq54242 eq702
    | (have j0 := eq702 (M.op x y) X0
       grind)
    | exact resolve eq702 eq54242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq54242
  have eq54432 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq54421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54421
  have eq54444 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq54432
    | (have j0 := eq54432 X0
       grind)
    | exact resolve eq54432 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54432
  have eq54451 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10317 eq54444
    | exact resolve eq54444 eq10317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54444
  have eq54744 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54272 eq36
    | exact resolve eq36 eq54272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq54272
  have eq54758 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq54744
    | exact resolve eq54744 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54744
  have eq54761 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10317 eq54758
    | exact resolve eq54758 eq10317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54758
  have eq54867 : y = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq50952 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq50952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50952
  have eq54892 : y = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq51379 eq54867
    | exact resolve eq54867 eq51379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54867
  have eq54910 : y = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq51379 eq54892
    | exact resolve eq54892 eq51379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51379 eq54892
  have eq54913 : y = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq50750 eq54910
    | exact resolve eq54910 eq50750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50750 eq54910
  have eq54914 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq54913
  have eq55095 : y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq190
       have i₂ := eq50720
       grind)
    | exact superpose eq50720 eq190
    | exact resolve eq190 eq50720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq50720
  have eq56364 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq54914 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq54914
       grind)
    | exact resolve eq13 eq54914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54914
  have eq56387 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq56364 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56364
  have eq56908 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54451 eq26
    | (have j1 := eq54451 (σ x)
       grind)
    | exact resolve eq26 eq54451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54451
  have eq57001 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54761 eq56908
    | exact resolve eq56908 eq54761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54761 eq56908
  have eq57045 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57001 eq27
    | exact resolve eq27 eq57001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57001
  have eq57160 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq57045
       have r₂ := eq10317
       grind)
    | exact resolve eq57045 eq10317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57045
  have eq57163 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57160 eq27
    | exact resolve eq27 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57166 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57160 eq191
    | exact resolve eq191 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq57171 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57160 eq681
    | (have r₁ := eq681
       have r₂ := eq57160
       grind)
    | exact resolve eq681 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq57261 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq57171
  have eq57369 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10317 eq57163
    | exact resolve eq57163 eq10317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10317 eq57163
  have eq57370 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq57369
  have eq57712 : x ≠ y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) := by grind
  clear eq55095
  have eq57725 : y ≠ (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq57160 eq57712
    | exact resolve eq57712 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57712
  have eq57738 : y ≠ (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq57160 eq57725
    | exact resolve eq57725 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57725
  have eq57743 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq57738
       have r₂ := eq51176
       grind)
    | exact resolve eq57738 eq51176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51176 eq57738
  have eq62309 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq57743
       have i₂ := eq51045 sF0
       grind)
    | exact superpose eq51045 eq57743
    | exact resolve eq57743 eq51045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57743
  have eq62332 : x ≠ (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq51045
  have eq62340 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq62309
  have eq62401 : (M.op x y) ≠ (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq57160 eq62332
    | exact resolve eq62332 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62332
  have eq62409 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq57160 eq62340
    | exact resolve eq62340 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62340
  have eq62564 : (M.op x y) ≠ (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq57160 eq62401
    | exact resolve eq62401 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62401
  have eq62567 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq51090 eq62409
    | exact resolve eq62409 eq51090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62409
  have eq62651 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq51090 eq62564
    | exact resolve eq62564 eq51090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51090 eq62564
  have eq62707 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62651
       have r₂ := eq62567
       grind)
    | exact resolve eq62651 eq62567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62567 eq62651
  have eq62835 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 y y
       have i₂ := eq62707
       grind)
    | exact superpose eq62707 eq180
    | exact resolve eq180 eq62707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq62707
  have eq76535 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56387 eq62835
    | exact resolve eq62835 eq56387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56387 eq62835
  have eq76581 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) := by grind
  clear eq76535
  have eq76700 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq51574 eq76581
    | exact resolve eq76581 eq51574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76581
  have eq76874 : y ≠ (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq76700
  have eq76891 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq76874
       have r₂ := eq51574
       grind)
    | exact resolve eq76874 eq51574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51574 eq76874
  have eq76919 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76891 eq42
    | exact resolve eq42 eq76891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq76940 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq76891 eq1612
    | (have j0 := eq1612 (M.op x y) (M.op x y) x
       grind)
    | exact resolve eq1612 eq76891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612 eq76891
  have eq76965 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq76940
    | (have j0 := eq76940 X0
       grind)
    | exact resolve eq76940 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76940
  have eq76969 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq76919
    | exact resolve eq76919 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76919
  have eq76971 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq76965 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq76965
    | (have j0 := eq76965 X0
       grind)
    | exact resolve eq76965 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76965
  have eq76975 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76969
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq76969
    | exact resolve eq76969 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq76969
  have eq76977 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq76971
    | (have j0 := eq76971 X0
       grind)
    | exact resolve eq76971 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76971
  have eq76981 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28 eq76977
    | (have j1 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq76977 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq76977
  have eq76983 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq76975 eq76981
    | exact resolve eq76981 eq76975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76975 eq76981
  have eq76984 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24911 eq76983
    | (have j0 := eq76983 X0
       have j1 := eq24911 X0
       grind)
    | exact resolve eq76983 eq24911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24911 eq76983
  have eq88355 : (σ y) = (M.op (σ x) (k (σ y) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57261 eq57166
    | exact resolve eq57166 eq57261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57166 eq57261
  have eq88448 : (σ y) = (M.op (σ x) (k (σ y) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq88355
  have eq90948 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76984 eq194
    | exact resolve eq194 eq76984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76984
  have eq91288 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq90948
  have eq91308 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq91288
       have r₂ := eq24915
       grind)
    | exact resolve eq91288 eq24915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24915 eq91288
  have eq91431 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq91308 eq194
    | exact resolve eq194 eq91308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq91308
  have eq104507 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4751 eq88448
    | exact resolve eq88448 eq4751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4751
  have eq104516 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq17546 eq88448
    | exact resolve eq88448 eq17546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17546 eq88448
  have eq104555 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq104516
  have eq104562 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq104507
  have eq104577 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26 eq104555
    | exact resolve eq104555 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104555
  have eq104582 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq104562
    | exact resolve eq104562 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104562
  have eq104589 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq57160 eq104577
    | exact resolve eq104577 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104577
  have eq104594 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq57160 eq104582
    | exact resolve eq104582 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57160 eq104582
  have eq104600 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq104589
       have r₂ := eq57370
       grind)
    | exact resolve eq104589 eq57370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104589
  have eq104605 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq104594
       have r₂ := eq57370
       grind)
    | exact resolve eq104594 eq57370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104594
  have eq104678 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq104600 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq104600
       grind)
    | exact resolve eq13 eq104600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104600
  have eq104712 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq104678 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104678
  have eq118008 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq104712 eq104605
    | exact resolve eq104605 eq104712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104605 eq104712
  have eq118043 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq118008
  have eq118088 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10499 eq118043
    | exact resolve eq118043 eq10499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10499 eq118043
  have eq118089 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq118088
  have eq118359 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq118089 eq142
    | exact resolve eq142 eq118089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq118089
  have eq118410 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq118359
    | exact resolve eq118359 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq118359
  have eq118426 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq630 x
       grind)
    | (have r₁ := eq118410
       have r₂ := eq630 x
       grind)
    | exact resolve eq118410 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq118410
  have eq118458 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10517
       have i₂ := eq118426
       grind)
    | exact superpose eq118426 eq10517
    | exact resolve eq10517 eq118426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10517
  have eq118506 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq118426
       grind)
    | exact superpose eq118426 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq118426
       grind)
    | exact resolve eq13 eq118426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118545 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq118506 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118506
  have eq118557 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq118458
  have eq119657 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118426
       have i₂ := eq118545 x
       grind)
    | exact superpose eq118545 eq118426
    | exact resolve eq118426 eq118545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118426 eq118545
  have eq119752 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq119657
  have eq119893 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39336
       have i₂ := eq119752
       grind)
    | exact superpose eq119752 eq39336
    | exact resolve eq39336 eq119752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39336 eq119752
  have eq119929 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq119893
  have eq119940 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq119929
       have r₂ := eq57370
       grind)
    | exact resolve eq119929 eq57370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57370 eq119929
  have eq120225 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119940 eq118557
    | exact resolve eq118557 eq119940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118557 eq119940
  have eq120321 : x = (M.op x y) := by grind
  clear eq120225
  have eq120330 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq120321
       grind)
    | exact superpose eq120321 eq22
    | exact resolve eq22 eq120321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq120321
  have eq120503 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq120330 eq20
    | exact resolve eq20 eq120330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq120330
  have eq120729 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120503 eq91431
    | exact resolve eq91431 eq120503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91431
  have eq120746 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq120729
    | exact resolve eq120729 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq120729
  have eq120747 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq120746
  have eq120807 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq120747 eq27
    | exact resolve eq27 eq120747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq120747
  have eq120949 : False := by grind
  exact eq120949
