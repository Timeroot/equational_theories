import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyx_pyx_pxy_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq14 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq10
    | exact resolve eq10 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq50
    | exact resolve eq50 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq69
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq69
    | exact resolve eq69 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq67
    | exact resolve eq67 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op y x) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq86 : (M.op y y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq99 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq103 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq65 sF3
       grind)
    | exact superpose eq65 eq99
    | exact resolve eq99 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq105 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq65 y
       grind)
    | exact superpose eq65 eq103
    | exact resolve eq103 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq103
  have eq124 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq16
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92 (σ X0)
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq92
    | exact resolve eq92 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq508 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq508
    | exact resolve eq508 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq519 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq514 X0
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq514
    | exact resolve eq514 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq514
  have eq586 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq51 X1 X4 x x
       have i₂ := eq51 X1 X0 x x
       grind)
    | (have i₁ := eq51 X0 X1 x x
       have i₂ := eq51 X0 (M.op x x) x x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X3 (M.op (M.op X4 X4) X0)) X3 X1 X2
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq51 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq51 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X2 X3 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq51 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq985 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq586 (σ X0) (σ X0) X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq586
    | exact resolve eq586 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq586 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq586
    | (have j0 := eq586 x y X0
       grind)
    | exact resolve eq586 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq586
    | (have j0 := eq586 X0 (σ y) (σ x)
       grind)
    | exact resolve eq586 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1040 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq988 (M.op X1 X1)
       have i₂ := eq52 y X0 X1
       grind)
    | (have i₁ := eq988 (M.op X1 X1)
       have i₂ := eq52 y X1 X0
       grind)
    | exact superpose eq52 eq988
    | exact resolve eq988 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq988
  have eq1093 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X0)) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq605 X2 (M.op X2 (M.op (M.op X3 X3) X0)) X1
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq605
    | exact resolve eq605 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1100 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq605 (σ X0) (σ X0) X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq605
    | exact resolve eq605 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1103 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq605 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq605
    | (have j0 := eq605 x y X0
       grind)
    | exact resolve eq605 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4983 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) X1) := by
    intro X0 X1
    first
    | exact superpose eq989 eq609
    | exact resolve eq609 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq989
  have eq8050 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq605 X2 X3 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)))
       have i₂ := eq591 X1 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq591 eq605
    | exact resolve eq605 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq25135 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq519 X0
       grind)
    | exact superpose eq519 eq985
    | exact resolve eq985 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq25168 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (σ X1))) = (σ (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25135 X1 X2
       have i₂ := eq586 X1 X1 X0
       grind)
    | (have i₁ := eq25135 X1 X2
       have i₂ := eq586 X0 X1 X1
       grind)
    | exact superpose eq586 eq25135
    | exact resolve eq25135 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq25135
  have eq25836 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1100 X0 X1
       have i₂ := eq519 X0
       grind)
    | exact superpose eq519 eq1100
    | exact resolve eq1100 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq1100
  have eq25901 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (σ X0)) = (σ (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25836 (M.op (M.op X1 X1) X0) X2
       have i₂ := eq14 X0 (M.op (M.op X1 X1) X0) X1
       grind)
    | exact superpose eq14 eq25836
    | exact resolve eq25836 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25836
  have eq44328 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1093 (M.op X1 X0) x X1 X2
       have i₂ := eq605 X1 X0 x
       grind)
    | exact superpose eq605 eq1093
    | exact resolve eq1093 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq45555 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44328 X1 X0 x
       have i₂ := eq4983 x (M.op X0 X1)
       grind)
    | exact superpose eq4983 eq44328
    | exact resolve eq44328 eq4983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4983 eq44328
  have eq49570 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (σ (M.op (M.op X1 X1) y)))) = (σ (M.op (M.op X2 X2) (M.op x (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25168 (M.op X2 X2) (M.op (M.op X1 X1) y) X0
       have i₂ := eq1040 X1 X2
       grind)
    | exact superpose eq1040 eq25168
    | exact resolve eq25168 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq25168
  have eq50012 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op (M.op X1 X1) y)))) := by
    intro X0 X1
    first
    | exact superpose eq1103 eq49570
    | exact resolve eq49570 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq49570
  have eq50040 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op (M.op X1 X1) y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50012 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq50012
    | (have j0 := eq50012 X0 X1
       grind)
    | exact resolve eq50012 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50012
  have eq50180 : ∀ X0 X2 : G, (M.op (M.op X0 X0) (σ y)) = (σ (M.op (M.op X2 X2) y)) := by
    intro X0 X2
    first
    | (have i₁ := eq605 x (σ (M.op (M.op X2 X2) y)) X0
       have i₂ := eq50040 x X2
       grind)
    | exact superpose eq50040 eq605
    | exact resolve eq605 eq50040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq50040
  have eq50528 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = (τ (M.op (M.op X0 X0) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X1 X1) y)
       have i₂ := eq50180 X0 X1
       grind)
    | exact superpose eq50180 eq16
    | exact resolve eq16 eq50180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52587 : ∀ X0 X1 : G, y = (M.op X1 (M.op X1 (τ (M.op (M.op X0 X0) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X1 x
       have i₂ := eq50528 X0 x
       grind)
    | exact superpose eq50528 eq14
    | exact resolve eq14 eq50528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50528
  have eq57921 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ x)) = (σ (M.op (M.op X1 X1) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq25901 x X1 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25901
    | (have j0 := eq25901 x X1 X0
       grind)
    | exact resolve eq25901 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25901
  have eq58543 : ∀ X0 X1 : G, (M.op (M.op X1 X1) x) = (τ (M.op (M.op X0 X0) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X1 X1) x)
       have i₂ := eq57921 X0 X1
       grind)
    | exact superpose eq57921 eq16
    | exact resolve eq16 eq57921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57921
  have eq58765 : ∀ X0 X1 : G, x = (M.op X1 (M.op X1 (τ (M.op (M.op X0 X0) (σ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X1 x
       have i₂ := eq58543 X0 x
       grind)
    | exact superpose eq58543 eq14
    | exact resolve eq14 eq58543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58543
  have eq107170 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op y (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq8050 X0 X1 y y
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq8050
    | exact resolve eq8050 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq107205 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq107170 x x
       have i₂ := eq8050 x x y x
       grind)
    | exact superpose eq8050 eq107170
    | exact resolve eq107170 eq8050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8050 eq107170
  have eq107245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq107205 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq107205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107205
  have eq107246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq107245
    | exact resolve eq107245 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107245
  have eq107257 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq107246
       have r₂ := eq28
       grind)
    | exact resolve eq107246 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107246
  have eq107507 : (σ y) = (M.op (σ y) (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq107257 eq45555
    | exact resolve eq45555 eq107257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107257
  have eq107512 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq45555 eq107507
    | exact resolve eq107507 eq45555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45555 eq107507
  have eq107555 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq107512 eq124
    | exact resolve eq124 eq107512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq107512
  have eq107852 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq29 eq107555
    | exact resolve eq107555 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq107555
  have eq107853 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq107852
  have eq108153 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq107853
       grind)
    | exact superpose eq107853 eq105
    | exact resolve eq105 eq107853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq108348 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq50180 X0 y
       have i₂ := eq107853
       grind)
    | exact superpose eq107853 eq50180
    | exact resolve eq50180 eq107853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50180 eq107853
  have eq108415 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq108348 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108348
    | (have j0 := eq108348 X0
       grind)
    | exact resolve eq108348 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108348
  have eq108466 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq108153
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq108153
    | exact resolve eq108153 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108153
  have eq108467 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq21 eq108415
    | (have j0 := eq108415 X0
       grind)
    | exact resolve eq108415 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108415
  have eq109947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq108466 eq108467
    | exact resolve eq108467 eq108466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108466 eq108467
  have eq110089 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq109947
  have eq110118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq110089
    | exact resolve eq110089 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110089
  have eq110128 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq110118
       have r₂ := eq28
       grind)
    | exact resolve eq110118 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110118
  have eq110233 : ∀ X0 X1 : G, y = (M.op X0 (M.op X0 (τ (M.op (M.op X1 X1) (σ x))))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq110128 eq52587
    | exact resolve eq52587 eq110128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52587 eq110128
  have eq110239 : x = y ∨ x = y := by
    first
    | exact superpose eq58765 eq110233
    | exact resolve eq110233 eq58765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58765 eq110233
  have eq110240 : x = y := by grind
  clear eq110239
  have eq110327 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq110240
       grind)
    | exact superpose eq110240 eq19
    | exact resolve eq19 eq110240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq110328 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq110240
       grind)
    | exact superpose eq110240 eq25
    | exact resolve eq25 eq110240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq110240
  have eq110506 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq110328
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq110328
    | exact resolve eq110328 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq110328
  have eq110535 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq110506 eq27
    | exact resolve eq27 eq110506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq110506
  have eq112582 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq110535 eq70
    | exact resolve eq70 eq110535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq110535
  have eq112941 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq112582
       have i₂ := eq110327
       grind)
    | exact superpose eq110327 eq112582
    | exact resolve eq112582 eq110327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110327 eq112582
  have eq112958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112941 eq15
    | exact resolve eq15 eq112941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112941
  have eq113047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq112958
    | exact resolve eq112958 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq112958
  have eq113068 : False := by grind
  exact eq113068

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pyx_pxy_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq14 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) X0)) ≠ X0 ∨ (k (M.op X1 (M.op (M.op X2 X2) X0)) X1) = (M.op (M.op X1 (M.op (M.op X2 X2) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op (M.op X2 X2) X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X1 (M.op (M.op X2 X2) X0)) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq45
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq45 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq74 y y
       grind)
    | exact superpose eq74 eq72
    | (have j1 := eq74 y y
       grind)
    | exact resolve eq72 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq106
    | exact resolve eq106 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq167 : (σ (k (k x x) y)) = (k (k (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq41 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq41
    | exact resolve eq41 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
  have eq305 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 X0
       have i₂ := eq74 X0 (τ X1)
       grind)
    | exact superpose eq74 eq39
    | (have j1 := eq74 X0 (τ X1)
       grind)
    | exact resolve eq39 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq388 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) X3 X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X2 (M.op X1 X1)
       have i₂ := eq52 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq14 X3 X2 (M.op X1 X1)
       have i₂ := eq52 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq237 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq237
    | (have j0 := eq237 X0 y
       grind)
    | exact resolve eq237 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq495 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq51 X1 X4 x x
       have i₂ := eq51 X1 X0 x x
       grind)
    | (have i₁ := eq51 X0 X1 x x
       have i₂ := eq51 X0 (M.op x x) x x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2))) = (M.op X5 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq51 (M.op X5 X2) X5 X3 X4
       have i₂ := eq51 X2 X5 X0 X1
       grind)
    | (have i₁ := eq51 (M.op (M.op X3 X3) X0) (M.op X2 X2) X2 X3
       have i₂ := eq51 X0 X1 X2 X3
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq51 X1 X0 x X4
       grind)
    | (have i₁ := eq14 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq51 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq51 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq51 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X2 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq51 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq107 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq597
    | exact resolve eq597 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq601 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq598
       have r₂ := eq28
       grind)
    | exact resolve eq598 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq644 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (σ (k X0 X0)) X2))) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq90 X0 X0
       grind)
    | exact superpose eq90 eq14
    | (have j1 := eq90 X0 X0
       grind)
    | exact resolve eq14 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq90 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  have eq669 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ x) X1))) = X1 ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq601 eq14
    | exact resolve eq14 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) ≠ (M.op X2 (M.op X0 (M.op X0 X1))) ∨ (k (M.op X2 (M.op X0 (M.op X0 X1))) X2) = (M.op (M.op X2 (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq64 (M.op (M.op x x) X0) X1 X2
       have i₂ := eq51 X0 X1 X2 x
       grind)
    | (have i₁ := eq64 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq51 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq51 eq64
    | exact resolve eq64 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq64
  have eq794 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X2) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq495 X1 (M.op X1 (M.op (M.op X2 X2) X0)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq495
    | exact resolve eq495 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (k X0 X1))) = (M.op X2 (M.op X2 (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq495 (σ X0) (σ X1) X2
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq495
    | (have j1 := eq90 X0 X1
       grind)
    | exact resolve eq495 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq806 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq495 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq495
    | (have j0 := eq495 x y X0
       grind)
    | exact resolve eq495 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq495
    | (have j0 := eq495 (σ x) (σ y) X0
       grind)
    | exact resolve eq495 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq601 eq495
    | exact resolve eq495 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq808 eq669
    | exact resolve eq669 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op y y) := by grind
  clear eq899
  have eq939 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op X0 X1))) = X1 ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq601 eq513
    | exact resolve eq513 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X0)) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq513 X2 (M.op X2 (M.op (M.op X3 X3) X0)) X1
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq513
    | exact resolve eq513 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq513 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq513
    | (have j0 := eq513 x y X0
       grind)
    | exact resolve eq513 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq513
    | (have j0 := eq513 (σ x) (σ y) X0
       grind)
    | exact resolve eq513 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1002 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) X0)) = (M.op (σ x) (M.op X1 X0)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq669 eq939
    | exact resolve eq939 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq1003 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ y) (σ x)))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq808 eq939
    | exact resolve eq939 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq939
  have eq1052 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ y) (σ x)))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1003 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1053 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) X0)) = (M.op (σ x) (M.op X1 X0)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq1002 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq3393 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1052 sF3
       have i₂ := eq495 sF3 sF2 x
       grind)
    | (have i₁ := eq1052 sF3
       have i₂ := eq495 X0 sF2 sF3
       grind)
    | exact superpose eq495 eq1052
    | exact resolve eq1052 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq4286 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X4 (M.op X4 (M.op X1 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq495 X1 (M.op X1 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X0)) X4
       have i₂ := eq396 X2 X3 X1 X0
       grind)
    | exact superpose eq396 eq495
    | exact resolve eq495 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq5371 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (M.op X1 (M.op X1 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq512
    | (have j0 := eq512 (σ x) (σ y) X1 X0
       grind)
    | exact resolve eq512 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7157 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X4 (M.op X4 (M.op X1 (M.op (M.op X2 (M.op X2 (M.op X3 X3))) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq495 X1 (M.op X1 (M.op (M.op X2 (M.op X2 (M.op X3 X3))) X0)) X4
       have i₂ := eq518 X2 X3 X1 X0
       grind)
    | exact superpose eq518 eq495
    | exact resolve eq495 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq7510 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq3393 eq1053
    | exact resolve eq1053 eq3393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053 eq3393
  have eq7547 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq7510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7510
  have eq8763 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq647 x
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq647
    | (have j0 := eq647 x
       grind)
    | exact resolve eq647 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8768 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8763
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8763
    | exact resolve eq8763 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8763
  have eq8773 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8768
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8768
    | exact resolve eq8768 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8768
  have eq11258 : ∀ X0 X1 X2 : G, (k (σ (M.op X2 X2)) X1) = (σ (M.op (M.op X0 X0) (τ X1))) ∨ (M.op X2 X2) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305 (M.op X2 X2) X1
       have i₂ := eq52 (τ X1) X0 X2
       grind)
    | (have i₁ := eq305 (M.op X2 X2) X1
       have i₂ := eq52 (τ X1) X2 X0
       grind)
    | exact superpose eq52 eq305
    | (have j0 := eq305 (M.op X2 X2) X1
       grind)
    | exact resolve eq305 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq18241 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (k (σ x) (σ x)) X1))) = X1 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq644 x X0 X1
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq644
    | (have j0 := eq644 x X1 x
       grind)
    | exact resolve eq644 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq18497 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (k (σ x) (σ x)) X1))) = X1 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq18241 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18241
    | (have j0 := eq18241 X0 X1
       grind)
    | exact resolve eq18241 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18241
  have eq19369 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X4 X4) (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3))) = (M.op X7 (M.op X7 (M.op X2 (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq512 X2 (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3)) X7 X4
       have i₂ := eq501 X5 X6 X3 X0 X1 X2
       grind)
    | (have i₁ := eq512 (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2)) X2 X4
       have i₂ := eq501 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq501 eq512
    | exact resolve eq512 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq512
  have eq19491 : ∀ X0 X1 X2 X3 X7 : G, (M.op X7 (M.op X7 (M.op X2 (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3 X7
    first
    | (have i₁ := eq19369 X0 X1 X2 X3 x x x X7
       have i₂ := eq388 X3 x x x
       grind)
    | exact superpose eq388 eq19369
    | exact resolve eq19369 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq19369
  have eq27862 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) ≠ (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (k (M.op X0 (M.op X0 (M.op X1 X2))) X1) = (M.op (M.op X0 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq734 X0 X1 X0 x
       have i₂ := eq495 X0 (M.op X0 X1) x
       grind)
    | (have i₁ := eq734 x X1 x x
       have i₂ := eq495 X0 (M.op x X1) x
       grind)
    | exact superpose eq495 eq734
    | exact resolve eq734 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq151222 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq668 eq107
    | exact resolve eq107 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq151228 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq151222
  have eq151318 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq151228 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq151228
       grind)
    | exact resolve eq13 eq151228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151228
  have eq151352 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq151318
  have eq151441 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq151352
    | exact resolve eq151352 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq151352
  have eq152962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq151441 eq107
    | exact resolve eq107 eq151441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq151441
  have eq152970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq152962
  have eq152973 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq152970
       have r₂ := eq28
       grind)
    | exact resolve eq152970 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152970
  have eq152978 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq152973 eq914
    | exact resolve eq914 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq153057 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq152973 eq7547
    | exact resolve eq7547 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7547 eq152973
  have eq153101 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op y y) := by grind
  clear eq153057
  have eq153180 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq152978
  have eq170969 : (M.op (σ x) (σ (M.op x y))) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) = (k (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq153101 eq13
    | (have j0 := eq13 (M.op (σ x) (σ (M.op x y))) (σ y)
       grind)
    | exact resolve eq13 eq153101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153101
  have eq171027 : (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) = (k (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq74 (M.op (σ x) (σ (M.op x y))) (σ y)
       grind)
    | (have r₁ := eq170969
       have r₂ := eq74 (M.op (σ x) (σ (M.op x y))) (σ y)
       grind)
    | exact resolve eq170969 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170969
  have eq496559 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq153180 eq171027
    | exact resolve eq171027 eq153180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153180 eq171027
  have eq496562 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq496559
  have eq496565 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq496562 eq84
    | exact resolve eq84 eq496562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496562
  have eq496580 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq601 eq496565
    | exact resolve eq496565 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq496565
  have eq496795 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) := by grind
  clear eq496580
  have eq496802 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq496795
    | exact resolve eq496795 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496795
  have eq502044 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq74 y y
       have i₂ := eq496802
       grind)
    | exact superpose eq496802 eq74
    | (have j0 := eq74 x y
       grind)
    | exact resolve eq74 eq496802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502045 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq502044
  have eq502435 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq502045
       grind)
    | exact superpose eq502045 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq502045
       grind)
    | exact resolve eq13 eq502045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502490 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq502045
  have eq502491 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq502435
  have eq502587 : x = y ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq496802
       have i₂ := eq502491
       grind)
    | exact superpose eq502491 eq496802
    | exact resolve eq496802 eq502491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496802 eq502491
  have eq502610 : x = y ∨ x = (M.op y y) := by grind
  clear eq502587
  have eq502622 : x = (M.op y y) := by
    first
    | (have r₁ := eq502610
       have r₂ := eq502490
       grind)
    | exact resolve eq502610 eq502490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502490 eq502610
  have eq502646 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq502622
       grind)
    | exact superpose eq502622 eq99
    | exact resolve eq99 eq502622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq502647 : (M.op y x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq806 y
       have i₂ := eq502622
       grind)
    | exact superpose eq502622 eq806
    | exact resolve eq806 eq502622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq502648 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 y
       have i₂ := eq502622
       grind)
    | exact superpose eq502622 eq14
    | exact resolve eq14 eq502622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502652 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 y
       have i₂ := eq502622
       grind)
    | exact superpose eq502622 eq52
    | exact resolve eq52 eq502622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq502686 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq513 X0 X1 y
       have i₂ := eq502622
       grind)
    | exact superpose eq502622 eq513
    | exact resolve eq513 eq502622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502717 : y = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq954 y
       have i₂ := eq502622
       grind)
    | exact superpose eq502622 eq954
    | exact resolve eq954 eq502622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502718 : (σ y) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq955 y
       have i₂ := eq502622
       grind)
    | exact superpose eq502622 eq955
    | exact resolve eq955 eq502622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502849 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq502622
       grind)
    | exact superpose eq502622 eq13
    | exact resolve eq13 eq502622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502899 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq502646
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq502646
    | exact resolve eq502646 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502646
  have eq502917 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op x (M.op x y))) = (M.op y (M.op (M.op X0 X0) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq943 x X1 y X0
       have i₂ := eq502647
       grind)
    | exact superpose eq502647 eq943
    | exact resolve eq943 eq502647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502960 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | exact superpose eq954 eq502917
    | exact resolve eq502917 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq502917
  have eq502973 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | exact superpose eq502717 eq513
    | exact resolve eq513 eq502717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq504491 : (τ (σ x)) = (k y y) ∨ x = y := by
    first
    | exact superpose eq502899 eq84
    | exact resolve eq84 eq502899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq502899
  have eq504510 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq504491
    | exact resolve eq504491 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504491
  have eq504513 : x = (k y y) := by
    first
    | (have r₁ := eq504510
       have r₂ := eq502849
       grind)
    | exact resolve eq504510 eq502849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502849 eq504510
  have eq504516 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq504513
       grind)
    | exact superpose eq504513 eq72
    | exact resolve eq72 eq504513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq504513
  have eq504571 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq504516
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq504516
    | exact resolve eq504516 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504516
  have eq504594 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq504571
       have i₂ := eq74 sF3 sF3
       grind)
    | exact superpose eq74 eq504571
    | (have j1 := eq74 (σ y) (σ y)
       grind)
    | exact resolve eq504571 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511005 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq502960 x
       have i₂ := eq502652 x x
       grind)
    | exact superpose eq502652 eq502960
    | exact resolve eq502960 eq502652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502960
  have eq511053 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = (M.op y (M.op (M.op X0 X0) (M.op x x))) := by
    intro X0 X1
    first
    | (have i₁ := eq943 (M.op x x) X1 y X0
       have i₂ := eq511005
       grind)
    | exact superpose eq511005 eq943
    | exact resolve eq943 eq511005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511114 : ∀ X1 : G, (M.op (M.op X1 X1) y) = (M.op y (M.op x (M.op x x))) := by
    intro X1
    first
    | (have i₁ := eq511053 x X1
       have i₂ := eq502652 (M.op x x) x
       grind)
    | exact superpose eq502652 eq511053
    | exact resolve eq511053 eq502652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511053
  have eq511148 : (M.op x y) = (M.op y (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq511114 x
       have i₂ := eq502973 x
       grind)
    | exact superpose eq502973 eq511114
    | exact resolve eq511114 eq502973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502973 eq511114
  have eq512521 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq511148
       have i₂ := eq495 x x X0
       grind)
    | (have i₁ := eq511148
       have i₂ := eq495 X0 x x
       grind)
    | exact superpose eq495 eq511148
    | exact resolve eq511148 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511148
  have eq518924 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq504594 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq504594
       grind)
    | exact resolve eq13 eq504594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518979 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq504594
  have eq518980 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq518924
  have eq519017 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq504571 eq518980
    | exact resolve eq518980 eq504571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504571 eq518980
  have eq519319 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq519017
       have r₂ := eq518979
       grind)
    | exact resolve eq519017 eq518979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518979 eq519017
  have eq519348 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq519319 eq807
    | exact resolve eq807 eq519319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519444 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq519319 eq955
    | exact resolve eq955 eq519319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519703 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq519319 eq502652
    | exact resolve eq502652 eq519319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520361 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op X0 X0) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq519348 eq943
    | exact resolve eq943 eq519348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520420 : ∀ X1 : G, (M.op (M.op X1 X1) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op x (σ x))) := by
    intro X1
    first
    | (have i₁ := eq520361 X1 X1
       have i₂ := eq502652 sF2 X1
       grind)
    | exact superpose eq502652 eq520361
    | exact resolve eq520361 eq502652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520361
  have eq520436 : (σ y) = (M.op (σ y) (M.op x (σ x))) := by
    first
    | exact superpose eq955 eq520420
    | exact resolve eq520420 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq520420
  have eq520736 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq519444 eq502686
    | exact resolve eq502686 eq519444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502686 eq519444
  have eq522125 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq519703 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq519703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527168 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (M.op (σ y) (M.op (M.op X0 X0) (M.op x (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq520436 eq943
    | exact resolve eq943 eq520436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq527236 : ∀ X1 : G, (M.op (M.op X1 X1) (σ y)) = (M.op (σ y) (M.op x (M.op x (σ x)))) := by
    intro X1
    first
    | (have i₁ := eq527168 X1 X1
       have i₂ := eq502652 (M.op x sF2) X1
       grind)
    | exact superpose eq502652 eq527168
    | exact resolve eq527168 eq502652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527168
  have eq527274 : (M.op x (σ y)) = (M.op (σ y) (M.op x (M.op x (σ x)))) := by
    first
    | (have i₁ := eq527236 x
       have i₂ := eq502652 sF3 x
       grind)
    | exact superpose eq502652 eq527236
    | exact resolve eq527236 eq502652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527236
  have eq527291 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op x (M.op x (σ x)))) := by
    first
    | exact superpose eq520736 eq527274
    | exact resolve eq527274 eq520736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527274
  have eq529099 : ∀ X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X1) (M.op X2 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq19491 x X1 X2 X3 x
       have i₂ := eq794 (M.op (M.op X1 X1) (M.op X2 X3)) X2 x x
       grind)
    | exact superpose eq794 eq19491
    | exact resolve eq19491 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq19491
  have eq529100 : ∀ X2 X3 : G, (M.op X2 (M.op x (M.op X2 X3))) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq529099 x X2 X3
       have i₂ := eq502652 (M.op X2 X3) x
       grind)
    | exact superpose eq502652 eq529099
    | exact resolve eq529099 eq502652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529099
  have eq529240 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq529100 X1 (M.op x (M.op X1 X0))
       have i₂ := eq529100 X1 X0
       grind)
    | exact superpose eq529100 eq529100
    | exact resolve eq529100 eq529100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530181 : (M.op x (σ x)) = (M.op (σ y) (M.op x (σ y))) := by
    first
    | exact superpose eq520436 eq529100
    | exact resolve eq529100 eq520436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520436
  have eq530627 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4286 X0 x X1 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq529100 (M.op (M.op X1 X1) (M.op X2 X2)) X0
       grind)
    | exact superpose eq529100 eq4286
    | exact resolve eq4286 eq529100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4286 eq529100
  have eq531181 : ∀ X0 X2 : G, (M.op x X0) = (M.op (M.op x (M.op X2 X2)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq530627 X0 x X2
       have i₂ := eq502652 (M.op X2 X2) x
       grind)
    | exact superpose eq502652 eq530627
    | exact resolve eq530627 eq502652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530627
  have eq531329 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op x (σ x)) := by
    first
    | exact superpose eq520736 eq530181
    | exact resolve eq530181 eq520736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530181
  have eq544005 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq527291
       have i₂ := eq495 x sF2 x
       grind)
    | (have i₁ := eq527291
       have i₂ := eq495 X0 sF2 x
       grind)
    | exact superpose eq495 eq527291
    | exact resolve eq527291 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq570436 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op (M.op x (M.op x (M.op X0 X0))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq5371 (M.op x (M.op X0 X0)) X1
       have i₂ := eq531181 (M.op x (M.op X0 X0)) X0
       grind)
    | exact superpose eq531181 eq5371
    | exact resolve eq5371 eq531181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5371 eq531181
  have eq571669 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op x (M.op (σ x) (σ y))))) = (M.op (M.op x (M.op x (M.op X0 X0))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq519703 eq570436
    | exact resolve eq570436 eq519703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570436
  have eq572224 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x (M.op x (M.op X0 X0))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq571669 X0 X0
       have i₂ := eq502648 X0 sF4
       grind)
    | exact superpose eq502648 eq571669
    | exact resolve eq571669 eq502648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502648 eq571669
  have eq622464 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq572224 eq7157
    | exact resolve eq7157 eq572224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7157 eq572224
  have eq660137 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ (k X0 (σ y))))) = (M.op X1 (M.op X1 (σ y))) ∨ (σ (τ X0)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq805 (τ X0) y X1
       have i₂ := eq422 X0
       grind)
    | exact superpose eq422 eq805
    | (have j0 := eq805 (τ X0) y x
       grind)
    | exact resolve eq805 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq805
  have eq662215 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ y))) = (M.op (σ (τ X0)) (σ (τ (k X0 (σ y))))) ∨ (σ (τ X0)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq660137 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq660137
    | (have j0 := eq660137 X0 X1
       grind)
    | exact resolve eq660137 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660137
  have eq662858 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ y))) = (M.op (σ (τ X0)) (k X0 (σ y))) ∨ (σ (τ X0)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq662215 X0 X1
       have i₂ := eq15 (k X0 sF3)
       grind)
    | exact superpose eq15 eq662215
    | (have j0 := eq662215 X0 X1
       grind)
    | exact resolve eq662215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662215
  have eq663320 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ y))) = (M.op X0 (k X0 (σ y))) ∨ (σ (τ X0)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq662858 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq662858
    | (have j0 := eq662858 X0 X1
       grind)
    | exact resolve eq662858 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662858
  have eq663670 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 (σ y))) ∨ (σ (τ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq807 eq663320
    | (have j0 := eq663320 X0 (σ x)
       grind)
    | exact resolve eq663320 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq663320
  have eq663836 : ∀ X0 : G, (M.op X0 (k X0 (σ y))) = (M.op x (M.op (σ x) (σ y))) ∨ (σ (τ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq519703 eq663670
    | (have j0 := eq663670 X0
       grind)
    | exact resolve eq663670 eq519703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663670
  have eq663925 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ y) (σ y)) ∨ (M.op X0 (k X0 (σ y))) = (M.op x (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq663836 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq663836
    | (have j0 := eq663836 X0
       grind)
    | exact resolve eq663836 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663836
  have eq663964 : ∀ X0 : G, (σ (τ X0)) = (σ x) ∨ (M.op X0 (k X0 (σ y))) = (M.op x (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq519319 eq663925
    | (have j0 := eq663925 X0
       grind)
    | exact resolve eq663925 eq519319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663925
  have eq663975 : ∀ X0 : G, (M.op X0 (k X0 (σ y))) = (M.op x (M.op (σ x) (σ y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq663964 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq663964
    | (have j0 := eq663964 X0
       grind)
    | exact resolve eq663964 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663964
  have eq758293 : ∀ X1 X2 : G, (k (σ (M.op X2 X2)) X1) = (σ (M.op x (τ X1))) ∨ (M.op X2 X2) = (M.op (τ X1) (τ X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq11258 x X1 X2
       have i₂ := eq502652 (τ X1) x
       grind)
    | exact superpose eq502652 eq11258
    | (have j0 := eq11258 x X1 X2
       grind)
    | exact resolve eq11258 eq502652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11258
  have eq758739 : ∀ X0 : G, (σ (M.op x (τ (σ y)))) = (σ (k (M.op X0 X0) y)) ∨ (M.op X0 X0) = (M.op (τ (σ y)) (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq41 (M.op x x)
       have i₂ := eq758293 sF3 x
       grind)
    | exact superpose eq758293 eq41
    | (have j1 := eq758293 (σ y) X0
       grind)
    | exact resolve eq41 eq758293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq758293
  have eq758740 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op X0 X0) y)) ∨ (M.op X0 X0) = (M.op (τ (σ y)) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq30 eq758739
    | (have j0 := eq758739 X0
       grind)
    | exact resolve eq758739 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758739
  have eq758966 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op X0 X0) y)) ∨ (M.op X0 X0) = (M.op (τ (σ y)) (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq758740 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq758740
    | (have j0 := eq758740 X0
       grind)
    | exact resolve eq758740 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq758740
  have eq759184 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op X0 X0) y)) ∨ (M.op X0 X0) = (M.op (τ (σ y)) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq21 eq758966
    | (have j0 := eq758966 X0
       grind)
    | exact resolve eq758966 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758966
  have eq759283 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) ∨ (σ (M.op x y)) = (σ (k (M.op X0 X0) y)) := by
    intro X0
    first
    | exact superpose eq30 eq759184
    | (have j0 := eq759184 X0
       grind)
    | exact resolve eq759184 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq759184
  have eq759373 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op X0 X0) y)) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq759283 X0
       have i₂ := eq502622
       grind)
    | exact superpose eq502622 eq759283
    | (have j0 := eq759283 X0
       grind)
    | exact resolve eq759283 eq502622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759283
  have eq787022 : ∀ X0 : G, (k (k (σ x) (σ x)) (σ y)) = (M.op X0 (M.op X0 (M.op x (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq663975 eq18497
    | (have j1 := eq663975 (M.op (σ x) (σ x))
       grind)
    | exact resolve eq18497 eq663975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18497 eq663975
  have eq787070 : ∀ X0 : G, (k (k (σ x) (σ x)) (σ y)) = (M.op X0 (M.op X0 (M.op x (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq787022 X0
       grind)
    | (have r₁ := eq787022 X0
       have r₂ := eq8773
       grind)
    | exact resolve eq787022 eq8773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8773 eq787022
  have eq787353 : (k (k (σ x) (σ x)) (σ y)) = (M.op x (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq622464 eq787070
    | exact resolve eq787070 eq622464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622464 eq787070
  have eq787553 : (M.op (σ x) (σ y)) = (k (k (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq520736 eq787353
    | exact resolve eq787353 eq520736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520736 eq787353
  have eq787688 : (M.op (σ x) (σ y)) = (k (k (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op x (σ x)) := by
    first
    | exact superpose eq519703 eq787553
    | exact resolve eq787553 eq519703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787553
  have eq1712841 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) ≠ (M.op x X2) ∨ (k (M.op X0 (M.op X0 (M.op X1 X2))) X1) = (M.op (M.op X0 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27862 X0 X1 X2 x
       have i₂ := eq502652 X2 x
       grind)
    | exact superpose eq502652 eq27862
    | (have j0 := eq27862 X0 X1 X2 x
       grind)
    | exact resolve eq27862 eq502652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27862
  have eq1715158 : (M.op x x) ≠ (M.op y y) ∨ (k (M.op y y) x) = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq1712841 y x x
       have i₂ := eq511005
       grind)
    | exact superpose eq511005 eq1712841
    | exact resolve eq1712841 eq511005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511005 eq1712841
  have eq1715965 : (k (M.op y y) x) = (M.op (M.op y y) x) := by
    first
    | (have j1 := eq74 (M.op y y) x
       grind)
    | (have r₁ := eq1715158
       have r₂ := eq74 (M.op y y) x
       grind)
    | (have r₁ := eq1715158
       have r₂ := eq74 (M.op x x) y
       grind)
    | exact resolve eq1715158 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1715158
  have eq1716987 : (M.op x x) = (k (M.op y y) x) := by
    first
    | (have i₁ := eq1715965
       have i₂ := eq502652 x y
       grind)
    | exact superpose eq502652 eq1715965
    | exact resolve eq1715965 eq502652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502652 eq1715965
  have eq1717860 : (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq1716987
       have i₂ := eq502622
       grind)
    | exact superpose eq502622 eq1716987
    | exact resolve eq1716987 eq502622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502622 eq1716987
  have eq1719080 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1717860
       grind)
    | exact superpose eq1717860 eq44
    | exact resolve eq44 eq1717860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1719085 : (k (k (σ x) (σ x)) (σ y)) = (σ (k (M.op x x) y)) := by
    first
    | (have i₁ := eq167
       have i₂ := eq1717860
       grind)
    | exact superpose eq1717860 eq167
    | exact resolve eq167 eq1717860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq1719110 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq647 x
       have i₂ := eq1717860
       grind)
    | exact superpose eq1717860 eq647
    | (have j0 := eq647 x
       grind)
    | exact resolve eq647 eq1717860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq1719319 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1719110
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1719110
    | exact resolve eq1719110 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719110
  have eq1719428 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1719319
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1719319
    | exact resolve eq1719319 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719319
  have eq1719455 : (σ x) = (M.op x (σ x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | exact superpose eq519703 eq1719428
    | exact resolve eq1719428 eq519703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719428
  have eq1719794 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq1719455
       have i₂ := eq1719080
       grind)
    | exact superpose eq1719080 eq1719455
    | exact resolve eq1719455 eq1719080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719455
  have eq1721307 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1719085
       have i₂ := eq759373 x
       grind)
    | exact superpose eq759373 eq1719085
    | (have j1 := eq759373 x
       grind)
    | exact resolve eq1719085 eq759373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759373 eq1719085
  have eq1723860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op x (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1721307 eq787688
    | exact resolve eq787688 eq1721307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787688 eq1721307
  have eq1723902 : (σ x) = (M.op x (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1723860
       have r₂ := eq28
       grind)
    | exact resolve eq1723860 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723860
  have eq1723915 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op x (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1723902 eq527291
    | exact resolve eq527291 eq1723902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527291 eq1723902
  have eq1724187 : (M.op (σ x) (σ y)) = (M.op x (M.op (σ y) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1723915
       have i₂ := eq529240 sF2 sF3
       grind)
    | exact superpose eq529240 eq1723915
    | exact resolve eq1723915 eq529240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723915
  have eq1724234 : (M.op (σ x) (σ y)) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq519348 eq1724187
    | exact resolve eq1724187 eq519348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724187
  have eq1724258 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq502718 eq1724234
    | exact resolve eq1724234 eq502718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724234
  have eq1724275 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1719080
       have i₂ := eq1724258
       grind)
    | exact superpose eq1724258 eq1719080
    | exact resolve eq1719080 eq1724258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719080 eq1724258
  have eq1725104 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1724275
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1724275
    | exact resolve eq1724275 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1724275
  have eq1725998 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op x (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1725104 eq1719794
    | (have r₁ := eq1719794
       have r₂ := eq1725104
       grind)
    | exact resolve eq1719794 eq1725104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719794 eq1725104
  have eq1726142 : (σ x) = (M.op x (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1725998
  have eq1727690 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op x (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1726142 eq544005
    | exact resolve eq544005 eq1726142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544005 eq1726142
  have eq1727854 : (M.op (σ x) (σ y)) = (M.op x (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1727690
       have i₂ := eq529240 sF2 sF3
       grind)
    | exact superpose eq529240 eq1727690
    | exact resolve eq1727690 eq529240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727690
  have eq1727917 : (M.op (σ x) (σ y)) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq519348 eq1727854
    | exact resolve eq1727854 eq519348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519348 eq1727854
  have eq1727944 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq502718 eq1727917
    | exact resolve eq1727917 eq502718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502718 eq1727917
  have eq1727945 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1727944
  have eq1727954 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1727945 eq28
    | exact resolve eq28 eq1727945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1728495 : (M.op (σ y) (σ y)) = (M.op x (σ x)) := by
    first
    | exact superpose eq1727945 eq531329
    | exact resolve eq531329 eq1727945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531329 eq1727945
  have eq1728575 : (σ x) = (M.op x (σ x)) := by
    first
    | exact superpose eq519319 eq1728495
    | exact resolve eq1728495 eq519319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519319 eq1728495
  have eq1728644 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1728575 eq522125
    | (have j0 := eq522125 (σ x)
       grind)
    | (have r₁ := eq522125 (σ x)
       have r₂ := eq1728575
       grind)
    | exact resolve eq522125 eq1728575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522125
  have eq1728831 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by grind
  clear eq1728644
  have eq1728913 : (k (σ x) (σ x)) = (M.op x (σ x)) := by
    first
    | exact superpose eq519703 eq1728831
    | exact resolve eq1728831 eq519703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519703 eq1728831
  have eq1728968 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1728575 eq1728913
    | exact resolve eq1728913 eq1728575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728575 eq1728913
  have eq1729129 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq1728968 eq50
    | exact resolve eq50 eq1728968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1728968
  have eq1729337 : (τ (σ x)) = (M.op x x) := by
    first
    | (have i₁ := eq1729129
       have i₂ := eq1717860
       grind)
    | exact superpose eq1717860 eq1729129
    | exact resolve eq1729129 eq1717860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717860 eq1729129
  have eq1729351 : x = (M.op x x) := by
    first
    | exact superpose eq29 eq1729337
    | exact resolve eq1729337 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1729337
  have eq1729640 : (M.op x y) = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq512521 x
       have i₂ := eq1729351
       grind)
    | exact superpose eq1729351 eq512521
    | exact resolve eq512521 eq1729351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512521 eq1729351
  have eq1730394 : (M.op x y) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq1729640
       have i₂ := eq529240 x y
       grind)
    | exact superpose eq529240 eq1729640
    | exact resolve eq1729640 eq529240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529240 eq1729640
  have eq1730573 : (M.op x y) = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq1730394
       have i₂ := eq502647
       grind)
    | exact superpose eq502647 eq1730394
    | exact resolve eq1730394 eq502647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502647 eq1730394
  have eq1730631 : y = (M.op x y) := by
    first
    | exact superpose eq502717 eq1730573
    | exact resolve eq1730573 eq502717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502717 eq1730573
  have eq1730658 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1730631 eq21
    | exact resolve eq21 eq1730631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1730631
  have eq1731201 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1730658
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1730658
    | exact resolve eq1730658 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1730658
  have eq1731286 : False := by grind
  exact eq1731286

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq44
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq50 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq50
  have eq194 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq199 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       have j1 := eq54 X1 X0
       grind)
    | (have r₁ := eq194 X1 X0
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq194 X1 X1
       have r₂ := eq54 X1 X1
       grind)
    | exact resolve eq194 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq194
  have eq277 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq199 (σ X1) (σ X0)
       grind)
    | exact superpose eq199 eq15
    | exact resolve eq15 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 X1
       have i₂ := eq199 X1 X0
       grind)
    | exact superpose eq199 eq277
    | exact resolve eq277 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq277
  have eq284 : False := by grind
  exact eq284

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq61 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq66 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq73
    | (have j1 := eq81 y x
       grind)
    | exact resolve eq73 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq81 sF3 sF2
       grind)
    | exact superpose eq81 eq80
    | (have j1 := eq81 (σ y) (σ x)
       grind)
    | exact resolve eq80 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq109 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq107
    | exact resolve eq107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq111 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq109
    | exact resolve eq109 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq112
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113 eq81
    | (have j0 := eq81 (σ y) (σ x)
       grind)
    | exact resolve eq81 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq124
  have eq135 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq22 eq37
  have eq140 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq62
    | exact resolve eq62 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq141 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq27
    | exact resolve eq27 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq135 eq16
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq428 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq73
    | exact resolve eq73 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq111
  have eq431 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq428
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq428
    | exact resolve eq428 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq479 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq66
    | (have r₁ := eq66
       have r₂ := eq126
       grind)
    | exact resolve eq66 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq126
  have eq480 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq479
  have eq481 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq480
       have r₂ := eq140
       grind)
    | exact resolve eq480 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq480
  have eq486 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq481 eq113
    | exact resolve eq113 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq481
  have eq490 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq486
  have eq497 : y = (M.op x y) := by
    first
    | (have r₁ := eq490
       have r₂ := eq141
       grind)
    | exact resolve eq490 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq490
  have eq500 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq497 eq20
    | exact resolve eq20 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq502 : x ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq497 eq61
    | exact resolve eq61 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq503 : y ≠ y ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq497 eq65
    | (have r₁ := eq65
       have r₂ := eq497
       grind)
    | exact resolve eq65 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq510 : x = y ∨ y = (k y x) := by grind
  clear eq503
  have eq518 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq500
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq500
    | exact resolve eq500 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq532 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq518 eq431
    | exact resolve eq431 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq535 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq532
       have r₂ := eq27
       grind)
    | exact resolve eq532 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq547 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq535 eq157
    | exact resolve eq157 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq535
  have eq549 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq497 eq547
    | exact resolve eq547 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq547
  have eq730 : x ≠ y ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq502
       have i₂ := eq549
       grind)
    | exact superpose eq549 eq502
    | exact resolve eq502 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq745 : y = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq510
       have i₂ := eq549
       grind)
    | exact superpose eq549 eq510
    | exact resolve eq510 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq549
  have eq746 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq745
       have r₂ := eq730
       grind)
    | exact resolve eq745 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq745
  have eq748 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq746 eq15
    | exact resolve eq15 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq762 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq748
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq748
    | exact resolve eq748 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq748
  have eq766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq518 eq762
    | exact resolve eq762 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq762
  have eq768 : False := by grind
  exact eq768

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pyx_pxy_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq19
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X2 X3 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq53 X2 X3 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op X1 (M.op (M.op X2 X2) X0)) X1) = (M.op (M.op X1 (M.op (M.op X2 X2) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X2 X2) X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op (M.op X2 X2) X0)) X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op (M.op X2 X2) X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 X3)) = (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X4 X2 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq52 X1 X4 x x
       have i₂ := eq52 X1 X0 x x
       grind)
    | (have i₁ := eq52 X0 X1 x x
       have i₂ := eq52 X0 (M.op x x) x x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X3 (M.op (M.op X4 X4) X0)) X3 X1 X2
       have i₂ := eq9 X0 X3 X4
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq52 X1 X0 x X4
       grind)
    | (have i₁ := eq9 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq52 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq52 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq52 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X3 (M.op X3 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq96 X2 (M.op X2 X1) X3
       have i₂ := eq96 X2 X1 X0
       grind)
    | (have i₁ := eq96 X2 (M.op X2 X1) X3
       have i₂ := eq96 X0 X1 X2
       grind)
    | exact superpose eq96 eq96
    | exact resolve eq96 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) (M.op X4 X1))) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X4 X1) X4 X2 X3
       have i₂ := eq96 X4 X1 X0
       grind)
    | (have i₁ := eq52 (M.op X4 X1) X4 X2 X3
       have i₂ := eq96 X0 X1 X4
       grind)
    | exact superpose eq96 eq52
    | exact resolve eq52 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq114 X2 X3 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq52 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq52 eq114
    | exact resolve eq114 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq114 X2 X3 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq114 X2 X3 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq114
    | exact resolve eq114 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X0)) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq114 X2 (M.op X2 (M.op (M.op X3 X3) X0)) X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq114
    | exact resolve eq114 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 X2) (M.op X3 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq114 X3 (M.op X3 X1) X2
       have i₂ := eq96 X3 X1 X0
       grind)
    | (have i₁ := eq114 X3 (M.op X3 X1) X2
       have i₂ := eq96 X0 X1 X3
       grind)
    | exact superpose eq96 eq114
    | exact resolve eq114 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq182
    | (have j0 := eq182 (σ X0) (σ X1)
       grind)
    | exact resolve eq182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq182 (σ X0) X1
       grind)
    | exact superpose eq182 eq29
    | (have j1 := eq182 (σ X0) X1
       grind)
    | exact resolve eq29 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq529 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq223 x y
       grind)
    | exact superpose eq223 eq16
    | (have j1 := eq223 x y
       grind)
    | exact resolve eq16 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (σ (k X0 X0)) X2))) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (σ X0)
       have i₂ := eq223 X0 X0
       grind)
    | exact superpose eq223 eq9
    | (have j1 := eq223 X0 X0
       grind)
    | exact resolve eq9 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq534 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X2 (σ X0)
       have i₂ := eq223 X0 X0
       grind)
    | exact superpose eq223 eq53
    | (have j1 := eq223 X0 X0
       grind)
    | exact resolve eq53 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (k X0 X1))) = (M.op X2 (M.op X2 (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96 X2 (σ X1) (σ X0)
       have i₂ := eq223 X0 X1
       grind)
    | exact superpose eq223 eq96
    | (have j1 := eq223 X0 X1
       grind)
    | exact resolve eq96 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (σ (k X0 X1))) = (M.op (M.op X2 X2) (M.op (M.op X3 X3) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (σ X1) (σ X0) X2 X3
       have i₂ := eq223 X0 X1
       grind)
    | exact superpose eq223 eq52
    | (have j1 := eq223 X0 X1
       grind)
    | exact resolve eq52 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq223
  have eq550 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq531 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq531
    | (have j0 := eq531 X0
       grind)
    | exact resolve eq531 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq652 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X4 (M.op X4 (M.op X2 (M.op X2 X0)))))) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq113 X4 (M.op X2 (M.op X2 X0)) X3 x
       have i₂ := eq114 X2 X0 x
       grind)
    | exact superpose eq114 eq113
    | exact resolve eq113 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op X3 X1)) = (M.op X4 (M.op X4 (M.op X3 (M.op X0 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq113 X3 (M.op X3 X1) X4 X2
       have i₂ := eq96 X3 X1 X0
       grind)
    | (have i₁ := eq113 X3 (M.op X3 X1) X4 X2
       have i₂ := eq96 X0 X1 X3
       grind)
    | exact superpose eq96 eq113
    | exact resolve eq113 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X1 X2 X1 X3
       have i₂ := eq96 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq113 X1 X2 X1 X3
       have i₂ := eq96 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq96 eq113
    | exact resolve eq113 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op X2 (M.op X3 (M.op X4 (M.op X4 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq96 X2 (M.op X3 (M.op X4 (M.op X4 X1))) X3
       have i₂ := eq113 X4 X1 X3 X0
       grind)
    | exact superpose eq113 eq96
    | exact resolve eq96 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1047 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op (M.op X1 (M.op X0 (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq118 X1 X1 X2 X3
       have i₂ := eq96 X1 X1 X0
       grind)
    | (have i₁ := eq118 X1 X1 X2 X3
       have i₂ := eq96 X0 X1 X1
       grind)
    | exact superpose eq96 eq118
    | exact resolve eq118 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1158 : ∀ X0 X1 : G, (k (M.op X0 (M.op (M.op X1 X1) X0)) X0) = (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1706 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) X4) = (M.op (M.op (M.op X5 X5) (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)))) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq64 X5 (M.op X1 (M.op X1 X2)) X4 X3
       have i₂ := eq131 X1 X2 (M.op X1 (M.op X1 X2)) X0
       grind)
    | exact superpose eq131 eq64
    | exact resolve eq64 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1810 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X3) X4) = (M.op (M.op (M.op X1 (M.op X1 X2)) X2) X4) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1706 x X1 X2 X3 X4 x
       have i₂ := eq114 x (M.op (M.op X1 (M.op X1 X2)) X2) x
       grind)
    | exact superpose eq114 eq1706
    | exact resolve eq1706 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq1840 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq529
       have i₂ := eq182 x y
       grind)
    | exact superpose eq182 eq529
    | (have j1 := eq182 (σ x) (σ y)
       grind)
    | exact resolve eq529 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq1843 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq1840
  have eq1863 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 (σ y) (σ y)
       have i₂ := eq1843
       grind)
    | exact superpose eq1843 eq12
    | exact resolve eq12 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1870 : (σ x) = (σ (k y y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1863
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq1863
    | exact resolve eq1863 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq2193 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op X0 X1))) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq183 X1 X1 X2 X3
       have i₂ := eq96 X1 X1 X0
       grind)
    | (have i₁ := eq183 X1 X1 X2 X3
       have i₂ := eq96 X0 X1 X1
       grind)
    | exact superpose eq96 eq183
    | exact resolve eq183 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq2676 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 (M.op X1 X0) x X1 X2
       have i₂ := eq114 X1 X0 x
       grind)
    | exact superpose eq114 eq186
    | exact resolve eq186 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq3639 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X4 X4) (M.op (M.op X1 (M.op X0 (M.op X0 X1))) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq88 X1 X1 X4 X3 X2
       have i₂ := eq96 X1 X1 X0
       grind)
    | (have i₁ := eq88 X1 X1 X4 X3 X2
       have i₂ := eq96 X0 X1 X1
       grind)
    | exact superpose eq96 eq88
    | exact resolve eq88 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq5110 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X4 (M.op X4 (M.op (M.op (M.op X0 X0) X1) X1))) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq116 X4 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) X2 X3
       have i₂ := eq101 X1 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq101 eq116
    | exact resolve eq116 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq10058 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1158 (M.op (M.op x x) (M.op x x)) (M.op x x)
       have i₂ := eq9 (M.op x x) (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq9 eq1158
    | exact resolve eq1158 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10091 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 (M.op X2 (M.op X3 X3))))) (M.op X2 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 (M.op X2 (M.op X3 X3))))) (M.op X2 (M.op X2 (M.op X3 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1158 (M.op X0 (M.op X0 (M.op X1 X1))) X1
       have i₂ := eq116 X0 X1 X2 (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X1 X1))))
       grind)
    | exact superpose eq116 eq1158
    | exact resolve eq1158 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1158
  have eq10111 : ∀ X1 X2 X3 : G, (k (M.op (M.op X1 X1) (M.op X3 X3)) (M.op X2 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X1 X1) (M.op X3 X3)) (M.op X2 (M.op X2 (M.op X3 X3)))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq10091 X2 X1 x X3
       have i₂ := eq187 x (M.op X3 X3) X2 (M.op X1 X1)
       grind)
    | exact superpose eq187 eq10091
    | exact resolve eq10091 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq10091
  have eq10125 : ∀ X1 X2 X3 : G, (M.op X3 X3) = (k (M.op (M.op X1 X1) (M.op X3 X3)) (M.op X2 (M.op X2 (M.op X3 X3)))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq10111 X1 X2 X3
       have i₂ := eq184 X1 X3 X2 (M.op X3 X3)
       grind)
    | exact superpose eq184 eq10111
    | exact resolve eq10111 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq10111
  have eq20776 : ∀ X0 X1 X2 X3 X4 : G, (σ (k (k X4 X4) X2)) = (M.op X3 (M.op X3 (M.op (M.op X0 X0) (M.op (M.op X1 X1) (σ X2))))) ∨ (σ X4) = (M.op (σ X4) (σ X4)) ∨ (M.op (σ X2) (σ X2)) = (σ (k X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq530 X4 X3 (σ (k (k X4 X4) X2))
       have i₂ := eq546 (k X4 X4) X2 X0 X1
       grind)
    | exact superpose eq546 eq530
    | (have j0 := eq530 X4 X1 X2
       have j1 := eq546 X4 X4 X2 X3
       grind)
    | exact resolve eq530 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq546
  have eq20967 : ∀ X1 X2 X4 : G, (M.op (M.op X1 X1) (σ X2)) = (σ (k (k X4 X4) X2)) ∨ (σ X4) = (M.op (σ X4) (σ X4)) ∨ (M.op (σ X2) (σ X2)) = (σ (k X4 X4)) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq20776 x X1 X2 x X4
       have i₂ := eq9 (M.op (M.op X1 X1) (σ X2)) x x
       grind)
    | exact superpose eq9 eq20776
    | (have j0 := eq20776 x X1 X2 x X4
       grind)
    | exact resolve eq20776 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20776
  have eq22708 : ∀ X0 : G, (σ X0) ≠ (σ (k (k X0 X0) X0)) ∨ (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (σ (k X0 X0)) (σ X0)
       have i₂ := eq550 X0
       grind)
    | exact superpose eq550 eq12
    | (have j0 := eq12 (σ (k X0 X0)) (σ X0)
       have j1 := eq550 X0
       grind)
    | (have r₁ := eq12 (σ (k X0 X0)) (σ X0)
       have r₂ := eq550 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq550 X0
       grind)
    | exact resolve eq12 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq22749 : ∀ X0 : G, (σ X0) ≠ (σ (k (k X0 X0) X0)) ∨ (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq22708 X0
       have j1 := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq22708 X0
       have r₂ := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq22708 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq22708 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22708
  have eq22761 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) ≠ (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22749 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq22749
    | (have j0 := eq22749 X0
       grind)
    | exact resolve eq22749 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22749
  have eq23066 : (k y (τ (σ y))) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq226 y (σ y)
       have i₂ := eq1843
       grind)
    | exact superpose eq1843 eq226
    | exact resolve eq226 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq1843
  have eq23119 : x = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23066
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23066
    | exact resolve eq23066 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23066
  have eq23124 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23119
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq23119
    | exact resolve eq23119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23119
  have eq39199 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq182 y y
       have i₂ := eq23124
       grind)
    | exact superpose eq23124 eq182
    | (have j0 := eq182 x y
       grind)
    | exact resolve eq182 eq23124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39200 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq39199
  have eq66139 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq39200
       grind)
    | exact superpose eq39200 eq12
    | (have r₁ := eq12 y y
       have r₂ := eq39200
       grind)
    | exact resolve eq12 eq39200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66192 : x ≠ y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq39200
  have eq66193 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq66139
  have eq80879 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23124
       have i₂ := eq66193
       grind)
    | exact superpose eq66193 eq23124
    | exact resolve eq23124 eq66193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23124 eq66193
  have eq80901 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq80879
  have eq80904 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq80901
       have r₂ := eq66192
       grind)
    | exact resolve eq80901 eq66192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66192 eq80901
  have eq147513 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1870
       have r₂ := eq80904
       grind)
    | exact resolve eq1870 eq80904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870 eq80904
  have eq147525 : (k y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq147513
       grind)
    | exact superpose eq147513 eq10
    | exact resolve eq10 eq147513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147513
  have eq147550 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq147525
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq147525
    | exact resolve eq147525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147525
  have eq147570 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq182 y y
       have i₂ := eq147550
       grind)
    | exact superpose eq147550 eq182
    | (have j0 := eq182 x y
       grind)
    | exact resolve eq182 eq147550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147571 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq147570
  have eq147776 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq147571
       grind)
    | exact superpose eq147571 eq12
    | (have r₁ := eq12 y y
       have r₂ := eq147571
       grind)
    | exact resolve eq12 eq147571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147844 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq147571
  have eq147845 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq147776
  have eq147849 : x = y ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq147550
       have i₂ := eq147845
       grind)
    | exact superpose eq147845 eq147550
    | exact resolve eq147550 eq147845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147550 eq147845
  have eq147877 : x = y ∨ x = (M.op y y) := by grind
  clear eq147849
  have eq147881 : x = (M.op y y) := by
    first
    | (have r₁ := eq147877
       have r₂ := eq147844
       grind)
    | exact resolve eq147877 eq147844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147844 eq147877
  have eq147896 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 y
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq9
    | exact resolve eq9 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147900 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 y
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq53
    | exact resolve eq53 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq147931 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1 y
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq114
    | exact resolve eq114 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq148047 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2676 X1 X0 y
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq2676
    | exact resolve eq2676 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148078 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq12
    | exact resolve eq12 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148079 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq96 y y X0
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq96
    | exact resolve eq96 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151287 : y = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq147931 y y
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq147931
    | exact resolve eq147931 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152217 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq692 x y x X0
       have i₂ := eq151287
       grind)
    | exact superpose eq151287 eq692
    | exact resolve eq692 eq151287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq152330 : (M.op x x) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq152217 x
       have i₂ := eq147900 x x
       grind)
    | exact superpose eq147900 eq152217
    | exact resolve eq152217 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152217
  have eq152569 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq148047 y y
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq148047
    | exact resolve eq148047 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153680 : y ≠ y ∨ (k (M.op x x) y) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq12 (M.op x x) y
       have i₂ := eq152569
       grind)
    | exact superpose eq152569 eq12
    | (have j0 := eq12 (M.op x x) y
       grind)
    | (have r₁ := eq12 (M.op x x) y
       have r₂ := eq152569
       grind)
    | exact resolve eq12 eq152569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152569
  have eq153750 : (k (M.op x x) y) = (M.op (M.op x x) y) := by grind
  clear eq153680
  have eq153796 : (M.op x y) = (k (M.op x x) y) := by
    first
    | (have i₁ := eq153750
       have i₂ := eq147900 y x
       grind)
    | exact superpose eq147900 eq153750
    | exact resolve eq153750 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153750
  have eq154171 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq147931 X0 (M.op X0 y)
       have i₂ := eq148079 X0
       grind)
    | exact superpose eq148079 eq147931
    | exact resolve eq147931 eq148079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154343 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq147896 X0 (M.op x y)
       have i₂ := eq148079 x
       grind)
    | exact superpose eq148079 eq147896
    | exact resolve eq147896 eq148079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148079
  have eq157592 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op x (M.op (M.op X1 (M.op X0 (M.op X0 X1))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3639 X0 X1 X2 X3 x
       have i₂ := eq147900 (M.op (M.op X1 (M.op X0 (M.op X0 X1))) X3) x
       grind)
    | exact superpose eq147900 eq3639
    | exact resolve eq3639 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3639
  have eq157654 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) = (M.op x (M.op (M.op X4 (M.op X5 (M.op X5 X4))) (M.op X3 (M.op X3 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq157592 X5 X4 X1 (M.op X3 (M.op X3 X2))
       have i₂ := eq131 X3 X2 X1 X0
       grind)
    | (have i₁ := eq157592 X0 X1 X3 (M.op X3 (M.op X2 X1))
       have i₂ := eq131 X0 X1 X2 X3
       grind)
    | exact superpose eq131 eq157592
    | exact resolve eq157592 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158608 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op x (M.op X0 (M.op (M.op X1 X1) X2))) = (M.op X3 (M.op X3 (M.op (M.op X4 (M.op X5 (M.op X5 X4))) (M.op X0 (M.op X6 (M.op X6 X2)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq157592 X5 X4 X3 (M.op (M.op X4 (M.op X5 (M.op X5 X4))) (M.op X0 (M.op X6 (M.op X6 X2))))
       have i₂ := eq768 X1 X2 (M.op X4 (M.op X5 (M.op X5 X4))) X0 X6
       grind)
    | exact superpose eq768 eq157592
    | exact resolve eq157592 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq158612 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op x (M.op X0 (M.op X1 (M.op X1 X2)))) = (M.op X3 (M.op X3 (M.op (M.op X4 (M.op X5 (M.op X5 X4))) (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq157592 X5 X4 X3 (M.op (M.op X4 (M.op X5 (M.op X5 X4))) (M.op X0 X2))
       have i₂ := eq131 X1 X2 X0 (M.op X4 (M.op X5 (M.op X5 X4)))
       grind)
    | (have i₁ := eq157592 X0 X1 X2 (M.op X0 (M.op X0 X1))
       have i₂ := eq131 X0 X1 (M.op X1 (M.op X0 (M.op X0 X1))) X3
       grind)
    | exact superpose eq131 eq157592
    | exact resolve eq157592 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq158876 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X4) (M.op X5 X3)) = (M.op X5 (M.op x (M.op (M.op X0 (M.op X1 (M.op X1 X0))) (M.op X2 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq663 X2 X3 X4 X5 X5
       have i₂ := eq157592 X1 X0 X5 (M.op X2 (M.op X2 X3))
       grind)
    | exact superpose eq157592 eq663
    | exact resolve eq663 eq157592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157592
  have eq159852 : ∀ X3 X4 X5 : G, (M.op (M.op X4 X4) (M.op X5 X3)) = (M.op X5 (M.op x X3)) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq158876 x x x X3 X4 X5
       have i₂ := eq2193 x x x X3
       grind)
    | exact superpose eq2193 eq158876
    | exact resolve eq158876 eq2193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158876
  have eq160024 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op x (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq158612 X0 X1 X2 x x x
       have i₂ := eq1047 x x x (M.op X0 X2)
       grind)
    | exact superpose eq1047 eq158612
    | exact resolve eq158612 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158612
  have eq160028 : ∀ X0 X1 X2 X6 : G, (M.op X0 (M.op X6 (M.op X6 X2))) = (M.op x (M.op X0 (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X6
    first
    | (have i₁ := eq158608 X0 X1 X2 x x x X6
       have i₂ := eq1047 x x x (M.op X0 (M.op X6 (M.op X6 X2)))
       grind)
    | exact superpose eq1047 eq158608
    | exact resolve eq158608 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq158608
  have eq160715 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq157654 X0 X1 X2 x x x
       have i₂ := eq2193 x x x X2
       grind)
    | exact superpose eq2193 eq157654
    | exact resolve eq157654 eq2193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193 eq157654
  have eq160925 : ∀ X3 X5 : G, (M.op X5 (M.op x X3)) = (M.op x (M.op X5 X3)) := by
    intro X3 X5
    first
    | (have i₁ := eq159852 X3 x X5
       have i₂ := eq147900 (M.op X5 X3) x
       grind)
    | exact superpose eq147900 eq159852
    | exact resolve eq159852 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159852
  have eq160977 : ∀ X0 X2 X6 : G, (M.op X0 (M.op X6 (M.op X6 X2))) = (M.op x (M.op X0 (M.op x X2))) := by
    intro X0 X2 X6
    first
    | (have i₁ := eq160028 X0 x X2 X6
       have i₂ := eq147900 X2 x
       grind)
    | exact superpose eq147900 eq160028
    | exact resolve eq160028 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160028
  have eq165814 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) ≠ X0 ∨ (k (M.op x X1) X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op x X1) X0
       have i₂ := eq160925 X1 X0
       grind)
    | (have i₁ := eq12 (M.op x x) x
       have i₂ := eq160925 x x
       grind)
    | exact superpose eq160925 eq12
    | (have j0 := eq12 (M.op x X1) X0
       grind)
    | exact resolve eq12 eq160925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174594 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) y) = (M.op x (M.op X0 (M.op X0 (M.op y (M.op X1 (M.op X1 x)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq154171 (M.op X2 X2)
       have i₂ := eq663 X1 x X2 y X0
       grind)
    | exact superpose eq663 eq154171
    | exact resolve eq154171 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq154171
  have eq175112 : ∀ X1 X2 : G, (M.op (M.op X2 X2) y) = (M.op y (M.op X1 (M.op X1 x))) := by
    intro X1 X2
    first
    | (have i₁ := eq174594 x X1 X2
       have i₂ := eq147931 x (M.op y (M.op X1 (M.op X1 x)))
       grind)
    | exact superpose eq147931 eq174594
    | exact resolve eq174594 eq147931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174594
  have eq175203 : ∀ X1 : G, (M.op x y) = (M.op y (M.op X1 (M.op X1 x))) := by
    intro X1
    first
    | (have i₁ := eq175112 X1 x
       have i₂ := eq147900 y x
       grind)
    | exact superpose eq147900 eq175112
    | exact resolve eq175112 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175112
  have eq202066 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X4 (M.op X4 (M.op (M.op x X1) X1))) X3) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq5110 x X1 X2 X3 X4
       have i₂ := eq147900 X1 x
       grind)
    | exact superpose eq147900 eq5110
    | exact resolve eq5110 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5110
  have eq202067 : ∀ X1 X3 X4 : G, (M.op x X3) = (M.op (M.op X4 (M.op X4 (M.op (M.op x X1) X1))) X3) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq202066 X1 x X3 X4
       have i₂ := eq147900 X3 x
       grind)
    | exact superpose eq147900 eq202066
    | exact resolve eq202066 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202066
  have eq202241 : ∀ X0 X1 X2 X3 : G, (M.op x X1) = (M.op (M.op (M.op x (M.op X2 (M.op X2 (M.op X3 (M.op X3 X0))))) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq202067 (M.op X2 (M.op X2 (M.op X3 (M.op X3 X0)))) X1 (M.op x (M.op X2 (M.op X2 (M.op X3 (M.op X3 X0)))))
       have i₂ := eq652 X0 X3 (M.op x (M.op X2 (M.op X2 (M.op X3 (M.op X3 X0))))) X2
       grind)
    | exact superpose eq652 eq202067
    | exact resolve eq202067 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq202067
  have eq204214 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op (M.op X3 (M.op X3 X0)) X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq202241 X0 X1 x X3
       have i₂ := eq147931 x (M.op X3 (M.op X3 X0))
       grind)
    | exact superpose eq147931 eq202241
    | exact resolve eq202241 eq147931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202241
  have eq217467 : ∀ X2 X3 : G, (M.op X3 X3) = (k (M.op x (M.op X3 X3)) (M.op X2 (M.op X2 (M.op X3 X3)))) := by
    intro X2 X3
    first
    | (have i₁ := eq10125 x X2 X3
       have i₂ := eq147900 (M.op X3 X3) x
       grind)
    | exact superpose eq147900 eq10125
    | exact resolve eq10125 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10125
  have eq217623 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op x (M.op X1 X1)) (M.op X1 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq217467 X1 X1
       have i₂ := eq96 X1 X1 X0
       grind)
    | (have i₁ := eq217467 X1 X1
       have i₂ := eq96 X0 X1 X1
       grind)
    | exact superpose eq96 eq217467
    | exact resolve eq217467 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq217467
  have eq245096 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) = (M.op X2 (M.op X2 (σ (τ X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq544 (τ X0) (τ X1) X2
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq544
    | (have j0 := eq544 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq544 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq544
  have eq246375 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq245096 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq245096
    | (have j0 := eq245096 X0 X1 X2
       grind)
    | exact resolve eq245096 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245096
  have eq246734 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq246375 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq246375
    | (have j0 := eq246375 X0 X1 X2
       grind)
    | exact resolve eq246375 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246375
  have eq246902 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op X0 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq246734 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246734
    | (have j0 := eq246734 X0 X1 X2
       grind)
    | exact resolve eq246734 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246734
  have eq246989 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X2 (M.op X2 X1)) = (M.op X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq246902 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246902
    | (have j0 := eq246902 X0 X1 X2
       grind)
    | exact resolve eq246902 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246902
  have eq247015 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op X0 (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq246989 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246989
    | (have j0 := eq246989 X0 X1 X2
       grind)
    | exact resolve eq246989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246989
  have eq305207 : ∀ X0 : G, (M.op y x) = (M.op X0 (k X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq247015 X0 y y
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq247015
    | exact resolve eq247015 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247015
  have eq310189 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op y x)))) = (M.op x (k X0 y)) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq160715 X1 X0 (k X0 y)
       have i₂ := eq305207 X0
       grind)
    | exact superpose eq305207 eq160715
    | (have j1 := eq305207 X0
       grind)
    | exact resolve eq160715 eq305207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160715 eq305207
  have eq310481 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op x (k X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq310189 X0 x
       have i₂ := eq154343 x
       grind)
    | exact superpose eq154343 eq310189
    | (have j0 := eq310189 X0 x
       grind)
    | exact resolve eq310189 eq154343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154343 eq310189
  have eq313376 : (M.op x x) = (M.op x (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq310481 y
       have i₂ := eq152330
       grind)
    | exact superpose eq152330 eq310481
    | (have j0 := eq310481 y
       grind)
    | exact resolve eq310481 eq152330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152330
  have eq315900 : (k y y) = (M.op x (M.op x (M.op x x))) ∨ x = y := by
    first
    | (have i₁ := eq148047 x (k y y)
       have i₂ := eq313376
       grind)
    | exact superpose eq313376 eq148047
    | exact resolve eq148047 eq313376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148047 eq313376
  have eq315921 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq315900
       have i₂ := eq147896 x x
       grind)
    | exact superpose eq147896 eq315900
    | exact resolve eq315900 eq147896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315900
  have eq316003 : x = (k y y) := by
    first
    | (have r₁ := eq315921
       have r₂ := eq148078
       grind)
    | exact resolve eq315921 eq148078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148078 eq315921
  have eq316120 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq534 y X1 X0
       have i₂ := eq316003
       grind)
    | exact superpose eq316003 eq534
    | (have j0 := eq534 y X1 x
       grind)
    | exact resolve eq534 eq316003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq316145 : ∀ X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) X1) = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq316120 x X1
       have i₂ := eq147900 X1 x
       grind)
    | exact superpose eq147900 eq316120
    | exact resolve eq316120 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316120
  have eq380798 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x (M.op X0 X0))) = (k (M.op X0 X0) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10058 x
       have i₂ := eq147900 (M.op x x) x
       grind)
    | exact superpose eq147900 eq10058
    | exact resolve eq10058 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10058
  have eq380799 : ∀ X0 : G, (M.op x (M.op (M.op X0 X0) (M.op X0 X0))) = (k (M.op X0 X0) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq380798 X0
       have i₂ := eq160925 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq160925 eq380798
    | exact resolve eq380798 eq160925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380798
  have eq380800 : ∀ X0 : G, (M.op x (M.op x (M.op X0 X0))) = (k (M.op X0 X0) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq380799 X0
       have i₂ := eq147900 (M.op X0 X0) X0
       grind)
    | exact superpose eq147900 eq380799
    | exact resolve eq380799 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380799
  have eq401835 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 (σ y) (σ y)
       have i₂ := eq316145 x
       grind)
    | exact superpose eq316145 eq12
    | (have j1 := eq316145 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq316145 x
       grind)
    | exact resolve eq12 eq316145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316145
  have eq401920 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq401835 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401835
  have eq401983 : ∀ X0 : G, (σ y) = (σ (k y y)) ∨ (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq401920 X0
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq401920
    | (have j0 := eq401920 X0
       grind)
    | exact resolve eq401920 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401920
  have eq402170 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq401983 X0
       have i₂ := eq316003
       grind)
    | exact superpose eq316003 eq401983
    | (have j0 := eq401983 X0
       grind)
    | exact resolve eq401983 eq316003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401983
  have eq402502 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq402170 (σ y)
       grind)
    | exact superpose eq402170 eq16
    | exact resolve eq16 eq402170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402170
  have eq503183 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (k (M.op x (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X2 (M.op X2 (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq217623 X0 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq161 X0 X1 (M.op X1 X1) X1 X1
       grind)
    | (have i₁ := eq217623 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq161 X0 X1 X2 x (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq161 eq217623
    | exact resolve eq217623 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq217623
  have eq505238 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (k (M.op x (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op x (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op x (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq503183 X0 X1 x
       have i₂ := eq160977 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq160977 eq503183
    | exact resolve eq503183 eq160977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160977 eq503183
  have eq506066 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (k (M.op x (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq505238 X0 X1
       have i₂ := eq2676 (M.op (M.op X0 X0) (M.op X0 X0)) x (M.op X0 X0)
       grind)
    | exact superpose eq2676 eq505238
    | exact resolve eq505238 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676 eq505238
  have eq506605 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (k (M.op x (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op x (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq506066 X0 X1
       have i₂ := eq147900 (M.op X0 X0) X0
       grind)
    | exact superpose eq147900 eq506066
    | exact resolve eq506066 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506066
  have eq506996 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (k (M.op X0 X0) (M.op x (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq506605 X0 X1
       have i₂ := eq160024 X0 X1 X0
       grind)
    | exact superpose eq160024 eq506605
    | exact resolve eq506605 eq160024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160024 eq506605
  have eq1058567 : ∀ X0 X1 : G, (M.op x (k (M.op X0 X0) (M.op x (M.op X0 X0)))) ≠ X0 ∨ (M.op (M.op x (M.op X1 (M.op X1 X0))) X0) = (k (M.op x (M.op X1 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq165814 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq506996 X0 X1
       grind)
    | exact superpose eq506996 eq165814
    | (have j0 := eq165814 X0 (M.op X1 (M.op X1 X0))
       grind)
    | (have r₁ := eq165814 (k (M.op x x) (M.op x (M.op x x))) (M.op (k (M.op x x) (M.op x (M.op x x))) x)
       have r₂ := eq506996 x (k (M.op x x) (M.op x (M.op x x)))
       grind)
    | exact resolve eq165814 eq506996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165814 eq506996
  have eq1059525 : ∀ X0 X1 : G, (M.op x (M.op x (M.op x (M.op X0 X0)))) ≠ X0 ∨ (M.op (M.op x (M.op X1 (M.op X1 X0))) X0) = (k (M.op x (M.op X1 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1058567 X0 X1
       have i₂ := eq380800 X0
       grind)
    | exact superpose eq380800 eq1058567
    | (have j0 := eq1058567 X0 X1
       grind)
    | exact resolve eq1058567 eq380800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380800 eq1058567
  have eq1059765 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op x (M.op X1 (M.op X1 X0))) X0) = (k (M.op x (M.op X1 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1059525 X0 X1
       have i₂ := eq147896 x (M.op X0 X0)
       grind)
    | exact superpose eq147896 eq1059525
    | (have j0 := eq1059525 X0 X1
       grind)
    | exact resolve eq1059525 eq147896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147896 eq1059525
  have eq1059881 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1059765 x X0
       have i₂ := eq147931 X0 x
       grind)
    | exact superpose eq147931 eq1059765
    | (have j0 := eq1059765 X0 x
       grind)
    | exact resolve eq1059765 eq147931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147931 eq1059765
  have eq1059922 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1059881 X0
       have j1 := eq182 X0 X0
       grind)
    | (have r₁ := eq1059881 X0
       have r₂ := eq182 X0 X0
       grind)
    | (have r₁ := eq1059881 (M.op x x)
       have r₂ := eq182 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq1059881 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1059881
  have eq1060121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1059922 (σ X0)
       grind)
    | exact superpose eq1059922 eq15
    | exact resolve eq15 eq1059922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060202 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1060121 X0
       have i₂ := eq1059922 X0
       grind)
    | exact superpose eq1059922 eq1060121
    | exact resolve eq1060121 eq1059922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060121
  have eq1061781 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X2 X3)) X3) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1810 X2 X3 (σ X0) X1
       have i₂ := eq1060202 X0
       grind)
    | exact superpose eq1060202 eq1810
    | exact resolve eq1810 eq1060202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810
  have eq1062201 : ∀ X0 X1 : G, (M.op x X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1061781 X0 X1 x x
       have i₂ := eq204214 x X1 x
       grind)
    | exact superpose eq204214 eq1061781
    | exact resolve eq1061781 eq204214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204214 eq1061781
  have eq1071120 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1062201 y X0
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq1062201
    | exact resolve eq1062201 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075263 : (M.op x (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1071120 (σ x)
       have i₂ := eq1060202 x
       grind)
    | exact superpose eq1060202 eq1071120
    | exact resolve eq1071120 eq1060202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075467 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1071120 (σ y)
       grind)
    | exact superpose eq1071120 eq16
    | exact resolve eq16 eq1071120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071120
  have eq1082548 : (M.op x x) = (τ (M.op x (σ x))) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1075263
       grind)
    | exact superpose eq1075263 eq10
    | exact resolve eq10 eq1075263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085276 : ∀ X1 X2 X4 : G, (M.op (M.op X1 X1) (σ X2)) = (σ (k (M.op X4 X4) X2)) ∨ (σ X4) = (M.op (σ X4) (σ X4)) ∨ (M.op (σ X2) (σ X2)) = (σ (k X4 X4)) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq20967 X1 X2 X4
       have i₂ := eq1059922 X4
       grind)
    | exact superpose eq1059922 eq20967
    | (have j0 := eq20967 X1 X2 X4
       grind)
    | exact resolve eq20967 eq1059922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20967
  have eq1085277 : ∀ X2 X4 : G, (M.op x (σ X2)) = (σ (k (M.op X4 X4) X2)) ∨ (σ X4) = (M.op (σ X4) (σ X4)) ∨ (M.op (σ X2) (σ X2)) = (σ (k X4 X4)) := by
    intro X2 X4
    first
    | (have i₁ := eq1085276 x X2 X4
       have i₂ := eq147900 (σ X2) x
       grind)
    | exact superpose eq147900 eq1085276
    | (have j0 := eq1085276 x X2 X4
       grind)
    | exact resolve eq1085276 eq147900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147900 eq1085276
  have eq1085278 : ∀ X2 X4 : G, (σ X4) = (σ (M.op X4 X4)) ∨ (M.op x (σ X2)) = (σ (k (M.op X4 X4) X2)) ∨ (M.op (σ X2) (σ X2)) = (σ (k X4 X4)) := by
    intro X2 X4
    first
    | (have i₁ := eq1085277 X2 X4
       have i₂ := eq1060202 X4
       grind)
    | exact superpose eq1060202 eq1085277
    | (have j0 := eq1085277 X2 X4
       grind)
    | exact resolve eq1085277 eq1060202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085277
  have eq1085279 : ∀ X2 X4 : G, (M.op (σ X2) (σ X2)) = (σ (M.op X4 X4)) ∨ (σ X4) = (σ (M.op X4 X4)) ∨ (M.op x (σ X2)) = (σ (k (M.op X4 X4) X2)) := by
    intro X2 X4
    first
    | (have i₁ := eq1085278 X2 X4
       have i₂ := eq1059922 X4
       grind)
    | exact superpose eq1059922 eq1085278
    | (have j0 := eq1085278 X2 X4
       grind)
    | exact resolve eq1085278 eq1059922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085278
  have eq1085280 : ∀ X2 X4 : G, (M.op x (σ X2)) = (σ (k (M.op X4 X4) X2)) ∨ (σ X4) = (σ (M.op X4 X4)) ∨ (σ (M.op X2 X2)) = (σ (M.op X4 X4)) := by
    intro X2 X4
    first
    | (have i₁ := eq1085279 X2 X4
       have i₂ := eq1060202 X2
       grind)
    | exact superpose eq1060202 eq1085279
    | (have j0 := eq1085279 X2 X4
       grind)
    | exact resolve eq1085279 eq1060202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085279
  have eq1089367 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1085280 y x
       have i₂ := eq153796
       grind)
    | exact superpose eq153796 eq1085280
    | (have j0 := eq1085280 y x
       grind)
    | exact resolve eq1085280 eq153796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085280
  have eq1089702 : (σ x) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1089367
       have r₂ := eq1075467
       grind)
    | exact resolve eq1089367 eq1075467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089367
  have eq1089983 : (σ x) = (M.op x (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1089702
       have i₂ := eq1075263
       grind)
    | exact superpose eq1075263 eq1089702
    | exact resolve eq1089702 eq1075263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089702
  have eq1090191 : (σ (M.op y y)) = (M.op x (σ x)) ∨ (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq1089983
       have i₂ := eq1075263
       grind)
    | exact superpose eq1075263 eq1089983
    | exact resolve eq1089983 eq1075263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089983
  have eq1090372 : (σ x) = (M.op x (σ x)) ∨ (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq1090191
       have i₂ := eq147881
       grind)
    | exact superpose eq147881 eq1090191
    | exact resolve eq1090191 eq147881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147881 eq1090191
  have eq1090373 : (σ x) = (M.op x (σ x)) := by grind
  clear eq1090372
  have eq1090885 : (τ (σ x)) = (M.op x x) := by
    first
    | (have i₁ := eq1082548
       have i₂ := eq1090373
       grind)
    | exact superpose eq1090373 eq1082548
    | exact resolve eq1082548 eq1090373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082548
  have eq1091178 : x = (M.op x x) := by
    first
    | (have i₁ := eq1090885
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1090885
    | exact resolve eq1090885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090885
  have eq1091499 : (M.op x y) = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq175203 x
       have i₂ := eq1091178
       grind)
    | exact superpose eq1091178 eq175203
    | exact resolve eq175203 eq1091178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175203 eq1091178
  have eq1092141 : (M.op x y) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq1091499
       have i₂ := eq160925 x y
       grind)
    | exact superpose eq160925 eq1091499
    | exact resolve eq1091499 eq160925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160925 eq1091499
  have eq1092334 : y = (M.op x y) := by
    first
    | (have i₁ := eq1092141
       have i₂ := eq151287
       grind)
    | exact superpose eq151287 eq1092141
    | exact resolve eq1092141 eq151287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151287 eq1092141
  have eq1093069 : (σ y) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq1075467
       have i₂ := eq1092334
       grind)
    | exact superpose eq1092334 eq1075467
    | exact resolve eq1075467 eq1092334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075467
  have eq1093681 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) ≠ (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22761 X0
       have i₂ := eq1059922 X0
       grind)
    | exact superpose eq1059922 eq22761
    | (have j0 := eq22761 X0
       grind)
    | exact resolve eq22761 eq1059922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22761
  have eq1093682 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op x (σ X0)) ∨ (σ X0) ≠ (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1093681 X0
       have i₂ := eq1062201 X0 (σ X0)
       grind)
    | exact superpose eq1062201 eq1093681
    | (have j0 := eq1093681 X0
       grind)
    | exact resolve eq1093681 eq1062201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062201 eq1093681
  have eq1093683 : ∀ X0 : G, (σ X0) ≠ (σ (k (M.op X0 X0) X0)) ∨ (σ (k (M.op X0 X0) X0)) = (M.op x (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1093682 X0
       have i₂ := eq1059922 X0
       grind)
    | exact superpose eq1059922 eq1093682
    | (have j0 := eq1093682 X0
       grind)
    | exact resolve eq1093682 eq1059922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059922 eq1093682
  have eq1093684 : ∀ X0 : G, (σ X0) ≠ (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k (M.op X0 X0) X0)) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1093683 X0
       have i₂ := eq1060202 X0
       grind)
    | exact superpose eq1060202 eq1093683
    | (have j0 := eq1093683 X0
       grind)
    | exact resolve eq1093683 eq1060202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060202 eq1093683
  have eq1093727 : (σ (M.op x y)) ≠ (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op x (k (M.op x y) y))) ∨ (M.op x (σ (M.op x y))) = (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1093684 (M.op x y)
       have i₂ := eq310481 (M.op x y)
       grind)
    | exact superpose eq310481 eq1093684
    | (have j1 := eq310481 (M.op x y)
       grind)
    | exact resolve eq1093684 eq310481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310481 eq1093684
  have eq1094115 : (σ y) ≠ (σ (k (M.op x (k y y)) y)) ∨ (σ (M.op x y)) = (σ (M.op x (k (M.op x y) y))) ∨ (M.op x (σ (M.op x y))) = (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1093727
       have i₂ := eq1092334
       grind)
    | exact superpose eq1092334 eq1093727
    | exact resolve eq1093727 eq1092334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093727
  have eq1094312 : (σ y) ≠ (σ (k (M.op x x) y)) ∨ (σ (M.op x y)) = (σ (M.op x (k (M.op x y) y))) ∨ (M.op x (σ (M.op x y))) = (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1094115
       have i₂ := eq316003
       grind)
    | exact superpose eq316003 eq1094115
    | exact resolve eq1094115 eq316003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094115
  have eq1094501 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ (M.op x (k (M.op x y) y))) ∨ (M.op x (σ (M.op x y))) = (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1094312
       have i₂ := eq153796
       grind)
    | exact superpose eq153796 eq1094312
    | exact resolve eq1094312 eq153796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094312
  have eq1094649 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ (M.op x (k (M.op x y) y))) ∨ (M.op x (σ (M.op x y))) = (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1094501
       have i₂ := eq1092334
       grind)
    | exact superpose eq1092334 eq1094501
    | exact resolve eq1094501 eq1092334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094501
  have eq1094650 : (σ (M.op x y)) = (σ (M.op x (k (M.op x y) y))) ∨ (M.op x (σ (M.op x y))) = (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1094649
  have eq1094783 : (σ y) = (σ (M.op x (k y y))) ∨ (M.op x (σ (M.op x y))) = (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1094650
       have i₂ := eq1092334
       grind)
    | exact superpose eq1092334 eq1094650
    | exact resolve eq1094650 eq1092334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094650
  have eq1094914 : (σ y) = (σ (M.op x x)) ∨ (M.op x (σ (M.op x y))) = (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1094783
       have i₂ := eq316003
       grind)
    | exact superpose eq316003 eq1094783
    | exact resolve eq1094783 eq316003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094783
  have eq1095016 : (σ y) = (M.op x (σ x)) ∨ (M.op x (σ (M.op x y))) = (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1094914
       have i₂ := eq1075263
       grind)
    | exact superpose eq1075263 eq1094914
    | exact resolve eq1094914 eq1075263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075263 eq1094914
  have eq1095098 : (σ x) = (σ y) ∨ (M.op x (σ (M.op x y))) = (σ (k (M.op x (k (M.op x y) y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1095016
       have i₂ := eq1090373
       grind)
    | exact superpose eq1090373 eq1095016
    | exact resolve eq1095016 eq1090373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095016
  have eq1095169 : (M.op x (σ y)) = (σ (k (M.op x (k y y)) y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1095098
       have i₂ := eq1092334
       grind)
    | exact superpose eq1092334 eq1095098
    | exact resolve eq1095098 eq1092334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095098
  have eq1095211 : (M.op x (σ y)) = (σ (k (M.op x x) y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1095169
       have i₂ := eq316003
       grind)
    | exact superpose eq316003 eq1095169
    | exact resolve eq1095169 eq316003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316003 eq1095169
  have eq1095241 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1095211
       have i₂ := eq153796
       grind)
    | exact superpose eq153796 eq1095211
    | exact resolve eq1095211 eq153796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153796 eq1095211
  have eq1095255 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1095241
       have r₂ := eq402502
       grind)
    | exact resolve eq1095241 eq402502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402502 eq1095241
  have eq1095261 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1095255
       have i₂ := eq1092334
       grind)
    | exact superpose eq1092334 eq1095255
    | exact resolve eq1095255 eq1092334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092334 eq1095255
  have eq1110032 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1095261
       grind)
    | exact superpose eq1095261 eq10
    | exact resolve eq10 eq1095261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095261
  have eq1110154 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1110032
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1110032
    | exact resolve eq1110032 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110032
  have eq1110155 : x = y := by grind
  clear eq1110154
  have eq1110348 : (σ x) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq1093069
       have i₂ := eq1110155
       grind)
    | exact superpose eq1110155 eq1093069
    | exact resolve eq1093069 eq1110155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093069 eq1110155
  have eq1110356 : False := by grind
  exact eq1110356

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq14 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq68
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq105
    | (have j0 := eq105 (σ X0)
       grind)
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq44
    | (have j1 := eq105 x
       grind)
    | exact resolve eq44 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq574 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq51 X1 X4 x x
       have i₂ := eq51 X1 X0 x x
       grind)
    | (have i₁ := eq51 X0 X1 x x
       have i₂ := eq51 X0 (M.op x x) x x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X3 (M.op (M.op X4 X4) X0)) X3 X1 X2
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq51 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq51 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X2 X3 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq51 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq52
  have eq656 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq574
    | (have j0 := eq574 X0 (σ y) (σ x)
       grind)
    | exact resolve eq574 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq856 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X0)) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq592 X2 (M.op X2 (M.op (M.op X3 X3) X0)) X1
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq592
    | exact resolve eq592 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4162 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) X1) := by
    intro X0 X1
    first
    | exact superpose eq656 eq597
    | exact resolve eq597 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq656
  have eq5054 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq463 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq7477 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq592 X2 X3 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)))
       have i₂ := eq579 X1 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq579 eq592
    | exact resolve eq592 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq38540 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq856 (M.op X1 X0) x X1 X2
       have i₂ := eq592 X1 X0 x
       grind)
    | exact superpose eq592 eq856
    | exact resolve eq856 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq856
  have eq39688 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38540 X1 X0 x
       have i₂ := eq4162 x (M.op X0 X1)
       grind)
    | exact superpose eq4162 eq38540
    | exact resolve eq38540 eq4162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4162 eq38540
  have eq66137 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op y (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq7477 X0 X1 y y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq7477
    | exact resolve eq7477 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq66164 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66137 x x
       have i₂ := eq7477 x x y x
       grind)
    | exact superpose eq7477 eq66137
    | exact resolve eq66137 eq7477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7477 eq66137
  have eq66205 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq66164 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq66164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq66205
    | exact resolve eq66205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66205
  have eq66217 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq66206
       have r₂ := eq28
       grind)
    | exact resolve eq66206 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66206
  have eq66363 : (σ y) = (M.op (σ y) (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq66217 eq39688
    | exact resolve eq39688 eq66217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66217
  have eq66368 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq39688 eq66363
    | exact resolve eq66363 eq39688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39688 eq66363
  have eq66403 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq66368
  have eq66585 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq66403
    | exact resolve eq66403 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66403
  have eq67622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq66585 eq66164
    | exact resolve eq66164 eq66585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66164 eq66585
  have eq67624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq67622
  have eq67626 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq67624
       have r₂ := eq28
       grind)
    | exact resolve eq67624 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67624
  have eq67887 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq468
       have i₂ := eq67626
       grind)
    | exact superpose eq67626 eq468
    | exact resolve eq468 eq67626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67891 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq67626
  have eq68033 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq67887
  have eq68073 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67891
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67891
    | exact resolve eq67891 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67891
  have eq68074 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68033
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq68033
    | exact resolve eq68033 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68033
  have eq68365 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq68073
       grind)
    | exact superpose eq68073 eq68
    | exact resolve eq68 eq68073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq68073
  have eq68383 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq68365
    | exact resolve eq68365 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68365
  have eq68384 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq68074
       have i₂ := eq105 sF2
       grind)
    | exact superpose eq105 eq68074
    | (have j1 := eq105 (σ x)
       grind)
    | exact resolve eq68074 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98258 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq68384
  have eq98460 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq98258
    | exact resolve eq98258 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98258
  have eq99463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98460 eq68383
    | exact resolve eq68383 eq98460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68383 eq98460
  have eq99465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq99463
  have eq99475 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq99465
       have r₂ := eq28
       grind)
    | exact resolve eq99465 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99465
  have eq99483 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq99709 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq99483 eq68074
    | exact resolve eq68074 eq99483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68074 eq99483
  have eq99724 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq99709
  have eq99738 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq99724 eq99475
    | exact resolve eq99475 eq99724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99475 eq99724
  have eq99905 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq99738
  have eq99957 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq99905 eq30
    | exact resolve eq30 eq99905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq99905
  have eq100108 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq99957
    | exact resolve eq99957 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq99957
  have eq100109 : x = y := by grind
  clear eq100108
  have eq100110 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq100109
       grind)
    | exact superpose eq100109 eq19
    | exact resolve eq19 eq100109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq100111 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq100109
       grind)
    | exact superpose eq100109 eq25
    | exact resolve eq25 eq100109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq100109
  have eq100360 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq100111
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq100111
    | exact resolve eq100111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100111
  have eq100362 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq100360 eq27
    | exact resolve eq27 eq100360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq100360
  have eq100523 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq468
       have i₂ := eq100110
       grind)
    | exact superpose eq100110 eq468
    | exact resolve eq468 eq100110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq100532 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq100742 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq100523
    | exact resolve eq100523 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100523
  have eq100766 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq101686 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100742 eq105
    | (have j0 := eq105 (σ x)
       grind)
    | exact resolve eq105 eq100742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq101687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100362 eq101686
    | exact resolve eq101686 eq100362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101686
  have eq101701 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq101687
       have r₂ := eq28
       grind)
    | exact resolve eq101687 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101687
  have eq101707 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100362 eq101701
    | exact resolve eq101701 eq100362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101701
  have eq101768 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101707 eq100766
    | exact resolve eq100766 eq101707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100766 eq101707
  have eq101775 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100362 eq101768
    | exact resolve eq101768 eq100362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101768
  have eq102239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101775 eq100742
    | exact resolve eq100742 eq101775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100742 eq101775
  have eq102244 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq102239
  have eq102247 : x = (M.op x y) := by
    first
    | (have r₁ := eq102244
       have r₂ := eq28
       grind)
    | exact resolve eq102244 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102244
  have eq102259 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq102247 eq21
    | exact resolve eq21 eq102247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq102458 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq102247 eq100532
    | exact resolve eq100532 eq102247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100532
  have eq102470 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq102458
       have i₂ := eq100110
       grind)
    | exact superpose eq100110 eq102458
    | exact resolve eq102458 eq100110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100110 eq102458
  have eq102627 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq102259
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq102259
    | exact resolve eq102259 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102259
  have eq102632 : x = (k x x) := by
    first
    | exact superpose eq102247 eq102470
    | exact resolve eq102470 eq102247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102247 eq102470
  have eq103401 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5054 x
       have i₂ := eq102632
       grind)
    | exact superpose eq102632 eq5054
    | (have j0 := eq5054 x
       grind)
    | exact resolve eq5054 eq102632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5054 eq102632
  have eq103405 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq103401
  have eq103414 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq103405
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq103405
    | exact resolve eq103405 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq103405
  have eq103429 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq100362 eq103414
    | exact resolve eq103414 eq100362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100362 eq103414
  have eq103442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102627 eq103429
    | exact resolve eq103429 eq102627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102627 eq103429
  have eq103453 : False := by grind
  exact eq103453

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyx_pyy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq14 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq68
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq105
    | (have j0 := eq105 (σ X0)
       grind)
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq44
    | (have j1 := eq105 x
       grind)
    | exact resolve eq44 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq574 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq51 X1 X4 x x
       have i₂ := eq51 X1 X0 x x
       grind)
    | (have i₁ := eq51 X0 X1 x x
       have i₂ := eq51 X0 (M.op x x) x x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X3 (M.op (M.op X4 X4) X0)) X3 X1 X2
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq51 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq51 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X2 X3 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq51 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq52
  have eq656 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq574
    | (have j0 := eq574 X0 (σ y) (σ x)
       grind)
    | exact resolve eq574 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq856 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X0)) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq592 X2 (M.op X2 (M.op (M.op X3 X3) X0)) X1
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq592
    | exact resolve eq592 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4162 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) X1) := by
    intro X0 X1
    first
    | exact superpose eq656 eq597
    | exact resolve eq597 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq656
  have eq5052 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq463 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq7471 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq592 X2 X3 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)))
       have i₂ := eq579 X1 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq579 eq592
    | exact resolve eq592 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq39025 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq856 (M.op X1 X0) x X1 X2
       have i₂ := eq592 X1 X0 x
       grind)
    | exact superpose eq592 eq856
    | exact resolve eq856 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq856
  have eq40167 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39025 X1 X0 x
       have i₂ := eq4162 x (M.op X0 X1)
       grind)
    | exact superpose eq4162 eq39025
    | exact resolve eq39025 eq4162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4162 eq39025
  have eq66592 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op y (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq7471 X0 X1 y y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq7471
    | exact resolve eq7471 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq66619 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66592 x x
       have i₂ := eq7471 x x y x
       grind)
    | exact superpose eq7471 eq66592
    | exact resolve eq66592 eq7471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7471 eq66592
  have eq66660 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq66619 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq66619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq66660
    | exact resolve eq66660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66660
  have eq66672 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq66661
       have r₂ := eq28
       grind)
    | exact resolve eq66661 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66661
  have eq66818 : (σ y) = (M.op (σ y) (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq66672 eq40167
    | exact resolve eq40167 eq66672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66672
  have eq66823 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq40167 eq66818
    | exact resolve eq66818 eq40167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40167 eq66818
  have eq66858 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq66823
  have eq67040 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq66858
    | exact resolve eq66858 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66858
  have eq68080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq67040 eq66619
    | exact resolve eq66619 eq67040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66619 eq67040
  have eq68082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq68080
  have eq68084 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq68082
       have r₂ := eq28
       grind)
    | exact resolve eq68082 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68082
  have eq68344 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq468
       have i₂ := eq68084
       grind)
    | exact superpose eq68084 eq468
    | exact resolve eq468 eq68084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68348 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq68084
  have eq68490 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq68344
  have eq68530 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68348
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68348
    | exact resolve eq68348 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68348
  have eq68531 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68490
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq68490
    | exact resolve eq68490 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68490
  have eq68832 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq68530
       grind)
    | exact superpose eq68530 eq68
    | exact resolve eq68 eq68530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq68530
  have eq68850 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq68832
    | exact resolve eq68832 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68832
  have eq68851 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq68531
       have i₂ := eq105 sF2
       grind)
    | exact superpose eq105 eq68531
    | (have j1 := eq105 (σ x)
       grind)
    | exact resolve eq68531 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99264 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq68851
  have eq99466 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq99264
    | exact resolve eq99264 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99264
  have eq100466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq99466 eq68850
    | exact resolve eq68850 eq99466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68850 eq99466
  have eq100468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq100466
  have eq100478 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq100468
       have r₂ := eq28
       grind)
    | exact resolve eq100468 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100468
  have eq100486 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq100712 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq100486 eq68531
    | exact resolve eq68531 eq100486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68531 eq100486
  have eq100727 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq100712
  have eq100741 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq100727 eq100478
    | exact resolve eq100478 eq100727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100478 eq100727
  have eq100908 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq100741
  have eq100958 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq100908 eq30
    | exact resolve eq30 eq100908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq100908
  have eq101109 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq100958
    | exact resolve eq100958 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq100958
  have eq101110 : x = y := by grind
  clear eq101109
  have eq101111 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq101110
       grind)
    | exact superpose eq101110 eq19
    | exact resolve eq19 eq101110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq101112 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq101110
       grind)
    | exact superpose eq101110 eq25
    | exact resolve eq25 eq101110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq101110
  have eq101361 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq101112
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq101112
    | exact resolve eq101112 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101112
  have eq101363 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq101361 eq27
    | exact resolve eq27 eq101361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq101361
  have eq101524 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq468
       have i₂ := eq101111
       grind)
    | exact superpose eq101111 eq468
    | exact resolve eq468 eq101111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq101533 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq101743 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq101524
    | exact resolve eq101524 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101524
  have eq101769 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq102685 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101743 eq105
    | (have j0 := eq105 (σ x)
       grind)
    | exact resolve eq105 eq101743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq102686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101363 eq102685
    | exact resolve eq102685 eq101363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102685
  have eq102700 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq102686
       have r₂ := eq28
       grind)
    | exact resolve eq102686 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102686
  have eq102706 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101363 eq102700
    | exact resolve eq102700 eq101363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102700
  have eq102767 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102706 eq101769
    | exact resolve eq101769 eq102706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101769 eq102706
  have eq102774 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101363 eq102767
    | exact resolve eq102767 eq101363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102767
  have eq103236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102774 eq101743
    | exact resolve eq101743 eq102774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101743 eq102774
  have eq103241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq103236
  have eq103244 : x = (M.op x y) := by
    first
    | (have r₁ := eq103241
       have r₂ := eq28
       grind)
    | exact resolve eq103241 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103241
  have eq103256 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq103244 eq21
    | exact resolve eq21 eq103244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq103455 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq103244 eq101533
    | exact resolve eq101533 eq103244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101533
  have eq103467 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq103455
       have i₂ := eq101111
       grind)
    | exact superpose eq101111 eq103455
    | exact resolve eq103455 eq101111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101111 eq103455
  have eq103624 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq103256
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq103256
    | exact resolve eq103256 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103256
  have eq103629 : x = (k x x) := by
    first
    | exact superpose eq103244 eq103467
    | exact resolve eq103467 eq103244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103244 eq103467
  have eq104398 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5052 x
       have i₂ := eq103629
       grind)
    | exact superpose eq103629 eq5052
    | (have j0 := eq5052 x
       grind)
    | exact resolve eq5052 eq103629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5052 eq103629
  have eq104402 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq104398
  have eq104411 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq104402
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq104402
    | exact resolve eq104402 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq104402
  have eq104426 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq101363 eq104411
    | exact resolve eq104411 eq101363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101363 eq104411
  have eq104439 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103624 eq104426
    | exact resolve eq104426 eq103624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103624 eq104426
  have eq104450 : False := by grind
  exact eq104450

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq186 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
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
  have eq187 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq186
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq186
    | exact resolve eq186 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq189 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq187
    | exact resolve eq187 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq189 eq178
    | exact resolve eq178 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq189
  have eq196 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq193
       have r₂ := eq27
       grind)
    | exact resolve eq193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq199 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq196 eq32
    | exact resolve eq32 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq196
  have eq216 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq199
    | exact resolve eq199 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq199
  have eq217 : x = y := by grind
  clear eq216
  have eq221 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq217
       grind)
    | exact superpose eq217 eq18
    | exact resolve eq18 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq222 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq217
       grind)
    | exact superpose eq217 eq24
    | exact resolve eq24 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq217
  have eq223 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq222
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq222
    | exact resolve eq222 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq226 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq223 eq26
    | exact resolve eq26 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq223
  have eq569 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq569 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq569 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq569 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq569 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq569 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq2541 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq221
       have i₂ := eq570 x
       grind)
    | exact superpose eq570 eq221
    | exact resolve eq221 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2547 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq226
       have i₂ := eq570 sF2
       grind)
    | exact superpose eq570 eq226
    | exact resolve eq226 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq570
  have eq2648 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq40
    | exact resolve eq40 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2541
  have eq2649 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2648
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2648
    | exact resolve eq2648 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2648
  have eq2651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2547 eq2649
    | exact resolve eq2649 eq2547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547 eq2649
  have eq2653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2651
    | exact resolve eq2651 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2651
  have eq2655 : False := by grind
  exact eq2655
