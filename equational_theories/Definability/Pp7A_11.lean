import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pyy_pyx_pxy_Equation1590 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1590 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq49
    | exact resolve eq49 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq73
    | exact resolve eq73 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
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
  clear eq44
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq20 eq89
    | exact resolve eq89 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq92 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq239 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
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
  have eq240 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq492 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X3 (M.op X0 X3))) (M.op X0 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X3 (M.op X0 X3))
       have i₂ := eq56 (M.op X1 X2) X3 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq683 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X3 X2 (M.op X2 (M.op X3 X0))
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op (M.op (M.op X1 (M.op X2 x)) (M.op (M.op X2 X1) X0)) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op (M.op X1 (M.op X2 x)) (M.op (M.op X2 X1) X0))
       have i₂ := eq52 x X2 X1 X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq708 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op y X0)) = (M.op (M.op X1 (M.op X2 x)) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (M.op (M.op X1 (M.op X2 x)) (M.op (M.op X2 X1) X0))
       have i₂ := eq52 x X2 X1 X0
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq709 : ∀ X0 X1 X2 : G, (σ y) = (M.op X0 (M.op (M.op (M.op X1 (M.op X2 (σ x))) (M.op (M.op X2 X1) X0)) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X2 (M.op X1 sF2)) (M.op (M.op X1 X2) x))
       have i₂ := eq52 sF2 X1 X2 x
       grind)
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq710 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op X1 (M.op X2 (σ x))) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X2 (M.op X1 sF2)) (M.op (M.op X1 X2) x))
       have i₂ := eq52 sF2 X1 X2 x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq767 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X2) (M.op (M.op (M.op X1 X0) X3) X4)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op X5 X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 (M.op (M.op X1 X0) X3) (M.op X3 X2) X5
       have i₂ := eq55 X2 X1 X0 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X1)) = (M.op (M.op x X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq240 eq55
    | exact resolve eq55 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq781 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1)) = (M.op (M.op (σ x) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq251 eq55
    | exact resolve eq55 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq796 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X2 X1) (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X3 (M.op X4 X0)) X2 X1 (M.op X4 X3)
       have i₂ := eq14 X0 X4 X3
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq825 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X2) (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X3 X2) (M.op (M.op X1 X0) X3) X4 X5
       have i₂ := eq55 X2 X1 X0 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq834 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op (M.op (M.op X1 X0) X3) X4)) = (M.op (M.op X1 X2) (M.op X0 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq767 X0 X1 X2 X3 X4 x
       have i₂ := eq55 X4 X0 (M.op X1 X2) x
       grind)
    | exact superpose eq55 eq767
    | exact resolve eq767 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq767
  have eq1088 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq351 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq351
    | exact resolve eq351 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq351
  have eq1123 : ∀ X0 : G, (τ (k X0 (M.op (σ x) (σ x)))) = (k (τ X0) (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1088 X0
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq1088
    | exact resolve eq1088 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1126 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq1123 X0
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq1123
    | exact resolve eq1123 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq9617 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op X0 (M.op (M.op x y) X0))) y) := by
    intro X0
    first
    | exact superpose eq239 eq492
    | exact resolve eq492 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq9628 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq250 eq492
    | exact resolve eq492 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq18136 : ∀ X1 X2 : G, y = (M.op (M.op X1 (M.op X2 x)) (M.op (M.op X2 X1) (M.op x y))) := by
    intro X1 X2
    first
    | (have i₁ := eq707 X1 X1 X2
       have i₂ := eq683 sF0 X1 (M.op X1 (M.op X2 x)) (M.op X2 X1)
       grind)
    | exact superpose eq683 eq707
    | exact resolve eq707 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq19329 : ∀ X1 X2 : G, (σ y) = (M.op (M.op X1 (M.op X2 (σ x))) (M.op (M.op X2 X1) (M.op (σ x) (σ y)))) := by
    intro X1 X2
    first
    | (have i₁ := eq709 X1 X1 X2
       have i₂ := eq683 sF4 X1 (M.op X1 (M.op X2 sF2)) (M.op X2 X1)
       grind)
    | exact superpose eq683 eq709
    | exact resolve eq709 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq709
  have eq47056 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X2) (M.op (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) (M.op X3 X5))) = X5 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq825 X0 X1 X2 X3 x X5
       have i₂ := eq834 X3 (M.op X1 X0) (M.op X0 (M.op X1 X2)) x X5
       grind)
    | exact superpose eq834 eq825
    | exact resolve eq825 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq834
  have eq47057 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X1 (M.op (M.op X1 X2) (M.op X0 (M.op X3 X5)))))) = X5 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq47056 X0 X1 X2 X3 X5
       have i₂ := eq796 (M.op X3 X5) X0 X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq796 eq47056
    | exact resolve eq47056 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq47056
  have eq63360 : (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (k x x) (M.op x x)) := by
    first
    | exact superpose eq49 eq1126
    | exact resolve eq1126 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1126
  have eq63396 : (k (M.op x x) (M.op x x)) = (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq63360
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq63360
    | exact resolve eq63360 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63360
  have eq63403 : (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq63396
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq63396
    | exact resolve eq63396 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63396
  have eq63406 : (M.op (M.op x x) (M.op x x)) = (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq63403
       have i₂ := eq69 (M.op x x)
       grind)
    | exact superpose eq69 eq63403
    | exact resolve eq63403 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63403
  have eq63409 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq63406
       have i₂ := eq69 (M.op sF2 sF2)
       grind)
    | exact superpose eq69 eq63406
    | exact resolve eq63406 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq63406
  have eq63412 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) := by
    first
    | exact superpose eq781 eq63409
    | exact resolve eq63409 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq63409
  have eq63414 : (M.op (M.op x y) (M.op y x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq63412
       have i₂ := eq780 x x
       grind)
    | exact superpose eq780 eq63412
    | exact resolve eq63412 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq63412
  have eq63587 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) = (σ (M.op (M.op x y) (M.op y x))) := by
    first
    | exact superpose eq63414 eq15
    | exact resolve eq15 eq63414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155430 : ∀ X0 X1 X2 : G, y = (M.op (M.op y X0) (M.op X1 (M.op X2 (M.op (M.op X2 X0) (M.op X1 (M.op y x)))))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47057 X1 X2 X0 y y
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq47057
    | exact resolve eq47057 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq155434 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq155430 x x x
       have i₂ := eq47057 x x x y x
       grind)
    | (have i₁ := eq155430 x x x
       have i₂ := eq47057 x x x x (M.op (M.op y x) (M.op x (M.op x (M.op (M.op x x) (M.op x (M.op y x))))))
       grind)
    | exact superpose eq47057 eq155430
    | exact resolve eq155430 eq47057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155430
  have eq155550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq155434 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq155434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155434
  have eq155563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq155550
    | exact resolve eq155550 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155550
  have eq155574 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq155563
       have r₂ := eq27
       grind)
    | exact resolve eq155563 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155563
  have eq155578 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq155574
    | exact resolve eq155574 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155574
  have eq155722 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op X2 (M.op (M.op X2 X0) (M.op X1 (M.op (σ y) (σ x))))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq155578 eq47057
    | exact resolve eq47057 eq155578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155578
  have eq155726 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq155722 x x x
       have i₂ := eq47057 x x x sF3 sF2
       grind)
    | (have i₁ := eq155722 x x x
       have i₂ := eq47057 x x x x (M.op (M.op sF3 x) (M.op x (M.op x (M.op (M.op x x) (M.op x (M.op sF3 sF2))))))
       grind)
    | exact superpose eq47057 eq155722
    | exact resolve eq155722 eq47057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47057 eq155722
  have eq155922 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op X1 X0) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq155726 eq19329
    | exact resolve eq19329 eq155726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19329 eq155726
  have eq155934 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq710 eq155922
    | exact resolve eq155922 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq155922
  have eq162955 : (τ (σ y)) = (M.op (M.op x y) (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq155934 eq63414
    | exact resolve eq63414 eq155934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63414 eq155934
  have eq163202 : y = (M.op (M.op x y) (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq162955
    | exact resolve eq162955 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162955
  have eq181081 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 (M.op (M.op x y) X0))) y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq163202 eq492
    | exact resolve eq492 eq163202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163202
  have eq181290 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9617 eq181081
    | exact resolve eq181081 eq9617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9617 eq181081
  have eq181291 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq181290
  have eq181392 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq181291 eq29
    | exact resolve eq29 eq181291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq181291
  have eq181668 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq181392
    | exact resolve eq181392 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq181392
  have eq181669 : x = (M.op x y) ∨ x = y := by grind
  clear eq181668
  have eq181694 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq181669 eq20
    | exact resolve eq20 eq181669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181855 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 x)) (M.op (M.op X1 X0) x)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq181669 eq18136
    | exact resolve eq18136 eq181669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18136 eq181669
  have eq181867 : y = (M.op (M.op x y) (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq181855 x x
       have i₂ := eq708 x x x
       grind)
    | exact superpose eq708 eq181855
    | exact resolve eq181855 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq181855
  have eq181972 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq181694
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq181694
    | exact resolve eq181694 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181694
  have eq184336 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ x = y := by
    first
    | exact superpose eq181867 eq63587
    | exact resolve eq63587 eq181867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63587 eq181867
  have eq184596 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq184336
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq184336
    | exact resolve eq184336 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184336
  have eq191323 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq184596 eq492
    | exact resolve eq492 eq184596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq184596
  have eq191539 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq9628 eq191323
    | exact resolve eq191323 eq9628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9628 eq191323
  have eq191630 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq191539 eq27
    | exact resolve eq27 eq191539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191539
  have eq191802 : x = y := by
    first
    | (have r₁ := eq191630
       have r₂ := eq181972
       grind)
    | exact resolve eq191630 eq181972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181972 eq191630
  have eq191815 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq191802
       grind)
    | exact superpose eq191802 eq18
    | exact resolve eq18 eq191802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq191816 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq191802
       grind)
    | exact superpose eq191802 eq24
    | exact resolve eq24 eq191802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq191802
  have eq192084 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq191816
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq191816
    | exact resolve eq191816 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq191816
  have eq192127 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq192084 eq26
    | exact resolve eq26 eq192084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq192084
  have eq193610 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq192127 eq74
    | exact resolve eq74 eq192127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq192127
  have eq193903 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq193610
       have i₂ := eq191815
       grind)
    | exact superpose eq191815 eq193610
    | exact resolve eq193610 eq191815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191815 eq193610
  have eq193975 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq193903 eq15
    | exact resolve eq15 eq193903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193903
  have eq194059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq193975
    | exact resolve eq193975 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq193975
  have eq194080 : False := by grind
  exact eq194080

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pxy_Equation1590 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1590 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x X0))) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq86 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq96 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq92
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq96
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq119
  have eq123 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq122
  have eq212 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op (M.op (M.op x y) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq212 eq14
    | exact resolve eq14 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq220 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x X0)) y) := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq427 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq531 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X2) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (M.op (M.op X1 X2) (M.op X2 X0)) X2 X1
       have i₂ := eq14 X0 X2 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq56 eq59
    | exact resolve eq59 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq533 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq563 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) X0) y) := by
    intro X0
    first
    | exact superpose eq532 eq14
    | exact resolve eq14 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq532 eq59
    | exact resolve eq59 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X3 X2 (M.op X2 (M.op X3 X0))
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X0 X1 X2
       have i₂ := eq59 (M.op (M.op X0 X1) X2) X1 X0
       grind)
    | exact superpose eq59 eq55
    | exact resolve eq55 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq752 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X2) (M.op (M.op (M.op X1 X0) X3) X4)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op X5 X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq58 X4 (M.op (M.op X1 X0) X3) (M.op X3 X2) X5
       have i₂ := eq58 X2 X1 X0 X3
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X1)) = (M.op (M.op x X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq213 eq58
    | exact resolve eq58 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq769 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1)) = (M.op (M.op (σ x) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq220 eq58
    | exact resolve eq58 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq786 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X2 X1) (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 (M.op X3 (M.op X4 X0)) X2 X1 (M.op X4 X3)
       have i₂ := eq14 X0 X4 X3
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X2) (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X3 X2) (M.op (M.op X1 X0) X3) X4 X5
       have i₂ := eq58 X2 X1 X0 X3
       grind)
    | exact superpose eq58 eq55
    | exact resolve eq55 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq830 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op (M.op (M.op X1 X0) X3) X4)) = (M.op (M.op X1 X2) (M.op X0 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq752 X0 X1 X2 X3 X4 x
       have i₂ := eq58 X4 X0 (M.op X1 X2) x
       grind)
    | exact superpose eq58 eq752
    | exact resolve eq752 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq876 : (M.op x y) = (M.op (M.op (M.op y x) (M.op (M.op x y) x)) y) := by
    first
    | exact superpose eq564 eq563
    | exact resolve eq563 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq564
  have eq1056 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq309 X0 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq309
    | exact resolve eq309 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq309
  have eq1358 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) (M.op X1 X2) X1
       have i₂ := eq531 X0 X1 X2
       grind)
    | exact superpose eq531 eq14
    | exact resolve eq14 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq1521 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X0)) = (M.op X1 (M.op (M.op X1 x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 (M.op (M.op X1 x) X0))
       have i₂ := eq688 X1 x X0
       grind)
    | exact superpose eq688 eq53
    | exact resolve eq53 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1529 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op X1 (M.op (M.op X1 (σ x)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X0 (M.op (M.op X0 sF2) x))
       have i₂ := eq688 X0 sF2 x
       grind)
    | exact superpose eq688 eq54
    | exact resolve eq54 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq2925 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op x (M.op (M.op X1 X0) X1))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq233 (M.op (M.op X1 X0) X1)
       have i₂ := eq1358 (M.op x (M.op (M.op X1 X0) X1)) X1 X0
       grind)
    | exact superpose eq1358 eq233
    | exact resolve eq233 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq2926 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (M.op (M.op X1 X0) X1))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq238 (M.op (M.op X1 x) X1)
       have i₂ := eq1358 (M.op sF2 (M.op (M.op X1 x) X1)) X1 x
       grind)
    | exact superpose eq1358 eq238
    | exact resolve eq238 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq1358
  have eq7151 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ (M.op (M.op x y) (M.op x y))) X0) (M.op X0 (σ (M.op y (M.op x (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq214 eq427
    | exact resolve eq427 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq427
  have eq7219 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op X0 (σ (M.op y (M.op x (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq123 eq7151
    | exact resolve eq7151 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq7151
  have eq7240 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op y (M.op x (M.op x y)))))) := by
    first
    | (have i₁ := eq7219 x
       have i₂ := eq58 (σ (M.op y (M.op x sF0))) sF1 sF1 x
       grind)
    | exact superpose eq58 eq7219
    | exact resolve eq7219 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq7219
  have eq11006 : (M.op x (M.op x y)) = (M.op (M.op y x) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq876 eq676
    | exact resolve eq676 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq876
  have eq14138 : y = (M.op (M.op (M.op x y) (M.op y x)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq11006 eq14
    | exact resolve eq14 eq11006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11006
  have eq60193 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X2) (M.op (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) (M.op X3 X5))) = X5 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq819 X0 X1 X2 X3 x X5
       have i₂ := eq830 X3 (M.op X1 X0) (M.op X0 (M.op X1 X2)) x X5
       grind)
    | exact superpose eq830 eq819
    | exact resolve eq819 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq830
  have eq60194 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X1 (M.op (M.op X1 X2) (M.op X0 (M.op X3 X5)))))) = X5 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq60193 X0 X1 X2 X3 X5
       have i₂ := eq786 (M.op X3 X5) X0 X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq786 eq60193
    | exact resolve eq60193 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq60193
  have eq69093 : (k (M.op x x) (M.op x x)) = (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq71 eq1056
    | exact resolve eq1056 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq69187 : (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (M.op x x) (M.op x x)) := by grind
  clear eq69093
  have eq69193 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by grind
  clear eq69187
  have eq69196 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) := by
    first
    | exact superpose eq769 eq69193
    | exact resolve eq69193 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq69193
  have eq69199 : (M.op (M.op x y) (M.op y x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq69196
       have i₂ := eq768 x x
       grind)
    | exact superpose eq768 eq69196
    | exact resolve eq69196 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq69196
  have eq140132 : ∀ X0 X1 X2 : G, (M.op (σ (M.op x y)) (σ (M.op y (M.op x (M.op x y))))) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (M.op X2 (M.op (M.op X2 X0) (M.op X1 (M.op (σ (M.op x y)) (σ (M.op x y)))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7240 eq60194
    | exact resolve eq60194 eq7240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7240
  have eq140133 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op x (M.op x y))))) := by
    first
    | (have i₁ := eq140132 x x x
       have i₂ := eq60194 x x x sF1 sF1
       grind)
    | (have i₁ := eq140132 x x x
       have i₂ := eq60194 x x x x (M.op (M.op sF1 x) (M.op x (M.op x (M.op (M.op x x) (M.op x (M.op sF1 sF1))))))
       grind)
    | exact superpose eq60194 eq140132
    | exact resolve eq140132 eq60194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60194 eq140132
  have eq153044 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ x = (k x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq86
       grind)
    | exact resolve eq12 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq153146 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ x = (k x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq153044
  have eq153147 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = y := by grind
  clear eq153146
  have eq273750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq153147 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq153147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153147
  have eq273760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq27 eq273750
    | exact resolve eq273750 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273750
  have eq273771 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have r₁ := eq273760
       have r₂ := eq28
       grind)
    | exact resolve eq273760 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273760
  have eq273803 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq273771 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq273771
       grind)
    | exact resolve eq12 eq273771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273771
  have eq273935 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = y := by grind
  clear eq273803
  have eq273936 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq273935
  have eq274149 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq273936 eq63
    | exact resolve eq63 eq273936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq273936
  have eq274177 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq29 eq274149
    | exact resolve eq274149 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274149
  have eq274178 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq274177
  have eq274184 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq274178
       grind)
    | exact superpose eq274178 eq49
    | exact resolve eq49 eq274178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq274193 : x = (M.op x y) ∨ (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq274178
       grind)
    | exact superpose eq274178 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq274178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274178
  have eq274202 : x = (M.op x y) ∨ (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq274193
  have eq274212 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq274202
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq274202
    | exact resolve eq274202 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274202
  have eq274221 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq274184
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq274184
    | exact resolve eq274184 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274184
  have eq274298 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq274221 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq274221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274221
  have eq274307 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq274298
  have eq274312 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq274307
    | exact resolve eq274307 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274307
  have eq275000 : (M.op x y) = (M.op (M.op x (M.op x (M.op (M.op x x) y))) y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2925 x y
       have i₂ := eq274212
       grind)
    | exact superpose eq274212 eq2925
    | exact resolve eq2925 eq274212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925 eq274212
  have eq275076 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq275000
       have i₂ := eq688 x x y
       grind)
    | exact superpose eq688 eq275000
    | exact resolve eq275000 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275000
  have eq275260 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq275076
       grind)
    | exact superpose eq275076 eq97
    | exact resolve eq97 eq275076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq275076
  have eq275566 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq275260
    | exact resolve eq275260 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275260
  have eq276091 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ y)))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq274312 eq2926
    | exact resolve eq2926 eq274312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926 eq274312
  have eq276167 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq276091
       have i₂ := eq688 sF2 sF2 sF3
       grind)
    | exact superpose eq688 eq276091
    | exact resolve eq276091 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq276091
  have eq276364 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq276167 eq275566
    | exact resolve eq275566 eq276167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275566 eq276167
  have eq276532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq276364
  have eq276632 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq276532
       have r₂ := eq28
       grind)
    | exact resolve eq276532 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276532
  have eq276734 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ x)) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq276632 eq533
    | exact resolve eq533 eq276632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq276632
  have eq276950 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1529 eq276734
    | exact resolve eq276734 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529 eq276734
  have eq293763 : (τ (σ y)) = (M.op (M.op x y) (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq276950 eq69199
    | exact resolve eq69199 eq276950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69199 eq276950
  have eq294084 : y = (M.op (M.op x y) (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq293763
    | exact resolve eq293763 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293763
  have eq302438 : x = (M.op (M.op y (M.op x y)) y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq294084 eq14
    | exact resolve eq14 eq294084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294084
  have eq302711 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq216 eq302438
    | exact resolve eq302438 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq302438
  have eq302712 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq302711
  have eq302887 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq302712 eq30
    | exact resolve eq30 eq302712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq302712
  have eq303261 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq302887
    | exact resolve eq302887 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq302887
  have eq303262 : x = (M.op x y) ∨ x = y := by grind
  clear eq303261
  have eq303321 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq303262 eq21
    | exact resolve eq21 eq303262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303392 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq303262 eq532
    | exact resolve eq532 eq303262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq303262
  have eq303642 : y = (M.op (M.op x y) (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq303392 x
       have i₂ := eq1521 x x
       grind)
    | exact superpose eq1521 eq303392
    | exact resolve eq303392 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq303392
  have eq303705 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq303321
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq303321
    | exact resolve eq303321 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303321
  have eq303782 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq303705 eq27
    | exact resolve eq27 eq303705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303705
  have eq305947 : y = (M.op y (M.op x (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq303642 eq14138
    | exact resolve eq14138 eq303642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14138 eq303642
  have eq316661 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq305947 eq140133
    | exact resolve eq140133 eq305947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140133 eq305947
  have eq316975 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq316661
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq316661
    | exact resolve eq316661 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316661
  have eq317183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq316975 eq303782
    | exact resolve eq303782 eq316975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303782 eq316975
  have eq317328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq317183
  have eq317399 : x = y := by
    first
    | (have r₁ := eq317328
       have r₂ := eq28
       grind)
    | exact resolve eq317328 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317328
  have eq317464 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq317399
       grind)
    | exact superpose eq317399 eq19
    | exact resolve eq19 eq317399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq317465 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq317399
       grind)
    | exact superpose eq317399 eq25
    | exact resolve eq25 eq317399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq317399
  have eq317845 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq317465
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq317465
    | exact resolve eq317465 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq317465
  have eq317969 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq317845 eq27
    | exact resolve eq27 eq317845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq317845
  have eq319124 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq317969 eq71
    | exact resolve eq71 eq317969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq317969
  have eq319486 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq319124
       have i₂ := eq317464
       grind)
    | exact superpose eq317464 eq319124
    | exact resolve eq319124 eq317464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317464 eq319124
  have eq319656 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq319486 eq15
    | exact resolve eq15 eq319486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319486
  have eq319740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq319656
    | exact resolve eq319656 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq319656
  have eq319761 : False := by grind
  exact eq319761

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pxy_pyx_Equation1590 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1590 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x X0))) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
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
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq120
  have eq124 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq123
  have eq163 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq215 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq223 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ y)
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq536 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq56 eq59
    | exact resolve eq59 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq536 eq59
    | exact resolve eq59 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq640 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq567 (M.op x (M.op sF0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq567
    | exact resolve eq567 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq738 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 X3) (M.op X3 X2)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 X3 (M.op X0 X3) X1
       have i₂ := eq59 X1 X3 X0
       grind)
    | exact superpose eq59 eq55
    | exact resolve eq55 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq59
  have eq1603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1603
    | exact resolve eq1603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq1607 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1604
       have r₂ := eq28
       grind)
    | exact resolve eq1604 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1609 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1607
    | exact resolve eq1607 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq1696 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1609 eq84
    | (have r₁ := eq84
       have r₂ := eq1609
       grind)
    | exact resolve eq84 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1697 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1609 eq223
    | exact resolve eq223 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq1704 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1696
  have eq1705 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1704
  have eq1809 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1705 eq105
    | exact resolve eq105 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq1705
  have eq1813 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1809
  have eq1911 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1813 eq1697
    | exact resolve eq1697 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq1930 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1911
  have eq1935 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1930 eq54
    | exact resolve eq54 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1930
  have eq2161 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1609 eq1935
    | exact resolve eq1935 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609 eq1935
  have eq2182 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2161
  have eq2290 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2182 eq14
    | exact resolve eq14 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2608 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1813 eq2290
    | exact resolve eq2290 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813 eq2290
  have eq2626 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2608
  have eq2628 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2626 eq163
    | exact resolve eq163 eq2626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq2626
  have eq2642 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq2628
    | exact resolve eq2628 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq2646 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2642 eq640
    | exact resolve eq640 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq2649 : y = (M.op (M.op x (M.op x y)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2642 eq56
    | exact resolve eq56 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2664 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2646
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2646
    | exact resolve eq2646 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2768 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2664 eq215
    | exact resolve eq215 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq2664
  have eq4341 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2768 eq2642
    | exact resolve eq2642 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2642 eq2768
  have eq4392 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4341
  have eq4411 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4392 eq2649
    | exact resolve eq2649 eq4392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649 eq4392
  have eq4441 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4411
  have eq4616 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq4441
       grind)
    | exact superpose eq4441 eq96
    | exact resolve eq96 eq4441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq4441
  have eq4635 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4616
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4616
    | exact resolve eq4616 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4616
  have eq4637 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4635 eq2182
    | exact resolve eq2182 eq4635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182 eq4635
  have eq4658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4637
  have eq4662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq4658
    | exact resolve eq4658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4658
  have eq4663 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq4662
       have r₂ := eq28
       grind)
    | exact resolve eq4662 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4662
  have eq4665 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4663 eq30
    | exact resolve eq30 eq4663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4663
  have eq4698 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq4665
    | exact resolve eq4665 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4665
  have eq4699 : x = (M.op x y) ∨ x = y := by grind
  clear eq4698
  have eq4878 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq4699 eq21
    | exact resolve eq21 eq4699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4881 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4699 eq56
    | exact resolve eq56 eq4699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq4699
  have eq4914 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq4878
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4878
    | exact resolve eq4878 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4878
  have eq8110 : ∀ X0 : G, (σ (M.op x x)) = (M.op (M.op (σ (M.op x x)) X0) (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq430 (M.op x x) X0
       have i₂ := eq4881 x
       grind)
    | exact superpose eq4881 eq430
    | exact resolve eq430 eq4881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq4881
  have eq8141 : ∀ X0 : G, (σ (M.op x x)) = (M.op (M.op (σ (M.op x x)) X0) (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8110 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8110
    | (have j0 := eq8110 X0
       grind)
    | exact resolve eq8110 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8110
  have eq8157 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8141 X0
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq8141
    | exact resolve eq8141 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq8141
  have eq8161 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq8157 x
       have i₂ := eq58 sF3 sF2 sF2 x
       grind)
    | exact superpose eq58 eq8157
    | exact resolve eq8157 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq8157
  have eq8162 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq27 eq8161
    | exact resolve eq8161 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8161
  have eq10048 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (M.op (σ x) X1) (M.op X1 X0)) (M.op (σ x) (σ x)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq8162 eq738
    | exact resolve eq738 eq8162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8162
  have eq10062 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10048 x x
       have i₂ := eq738 sF2 sF2 x x
       grind)
    | exact superpose eq738 eq10048
    | exact resolve eq10048 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq10048
  have eq10073 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq10062 eq28
    | exact resolve eq28 eq10062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10062
  have eq10114 : x = y := by
    first
    | (have r₁ := eq10073
       have r₂ := eq4914
       grind)
    | exact resolve eq10073 eq4914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4914 eq10073
  have eq10115 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq10114
       grind)
    | exact superpose eq10114 eq19
    | exact resolve eq19 eq10114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq10116 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq10114
       grind)
    | exact superpose eq10114 eq25
    | exact resolve eq25 eq10114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq10114
  have eq10157 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10116
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10116
    | exact resolve eq10116 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10116
  have eq10632 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10157 eq27
    | exact resolve eq27 eq10157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10157
  have eq10756 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq10632 eq71
    | exact resolve eq71 eq10632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq10632
  have eq10818 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10756
       have i₂ := eq10115
       grind)
    | exact superpose eq10115 eq10756
    | exact resolve eq10756 eq10115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10115 eq10756
  have eq10824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10818 eq15
    | exact resolve eq15 eq10818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10818
  have eq10866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10824
    | exact resolve eq10824 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq10824
  have eq10875 : False := by grind
  exact eq10875

/-- `Equation1630`: `x = (x ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_x_pxy_Equation1630 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1630 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1630.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq573 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq548
    | (have j0 := eq548 X0 X1
       grind)
    | exact resolve eq548 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq587 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq573
    | (have j0 := eq573 X0 X1
       grind)
    | exact resolve eq573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq2911 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq587
    | (have j0 := eq587 (τ X0) X1
       grind)
    | exact resolve eq587 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq2970 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2911 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq2911
    | (have j0 := eq2911 X0 X1
       grind)
    | exact resolve eq2911 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911
  have eq2998 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2970 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq2970
    | (have j0 := eq2970 X0 X1
       grind)
    | exact resolve eq2970 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2970
  have eq3377 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) X1
       have i₂ := eq2998 (σ X1) X0
       grind)
    | exact superpose eq2998 eq28
    | (have j1 := eq2998 (σ X1) X0
       grind)
    | exact resolve eq28 eq2998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2998
  have eq3418 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3377 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3377
    | (have j0 := eq3377 X0 X1
       grind)
    | exact resolve eq3377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377
  have eq3444 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3418 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq3418
    | (have j0 := eq3418 X0 X1
       grind)
    | exact resolve eq3418 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3418
  have eq6168 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) X2)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106 X0 X1
       have i₂ := eq3444 X0 X1
       grind)
    | (have i₁ := eq106 X1 X1
       have i₂ := eq3444 X0 X1
       grind)
    | exact superpose eq3444 eq106
    | (have j1 := eq3444 X0 X1
       grind)
    | exact resolve eq106 eq3444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq6249 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6168 X0 X1 x
       have i₂ := eq106 X0 x
       grind)
    | exact superpose eq106 eq6168
    | (have j0 := eq6168 X0 X1 x
       grind)
    | exact resolve eq6168 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq6168
  have eq6250 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq6249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6249
  have eq6298 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6250 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6250
    | exact resolve eq6250 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6361 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq6250 X0 X1
       grind)
    | exact superpose eq6250 eq11
    | (have j1 := eq6250 X0 X1
       grind)
    | exact resolve eq11 eq6250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6250
  have eq6457 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6298 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6298
    | exact resolve eq6298 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6298
  have eq6584 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6457 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq6457
    | (have j0 := eq6457 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq6457 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq6457
  have eq6640 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq6584 X1 X0
       grind)
    | exact superpose eq6584 eq11
    | (have j1 := eq6584 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6584
  have eq6764 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6640 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq6640
    | (have j0 := eq6640 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq6640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6640
  have eq6794 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq6764 X0 (τ X1)
       grind)
    | exact superpose eq6764 eq19
    | (have j1 := eq6764 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq6764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq6764
  have eq7803 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6794 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6794
    | exact resolve eq6794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6794
  have eq7888 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7803 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7803
    | (have j0 := eq7803 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq7803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7803
  have eq8359 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6361 x y
       grind)
    | exact superpose eq6361 eq16
    | (have j1 := eq6361 x y
       grind)
    | exact resolve eq16 eq6361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6361
  have eq8410 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8359
       have i₂ := eq7888 y x
       grind)
    | exact superpose eq7888 eq8359
    | (have j1 := eq7888 (σ x) (σ y)
       grind)
    | (have r₁ := eq8359
       have r₂ := eq7888 y x
       grind)
    | (have r₁ := eq8359
       have r₂ := eq7888 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8359
       have r₂ := eq7888 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8359 eq7888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7888 eq8359
  have eq8413 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq8410
  have eq8416 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8413
       grind)
    | exact superpose eq8413 eq16
    | exact resolve eq16 eq8413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8413
  have eq8417 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq8416
       have r₂ := eq22 x
       grind)
    | exact resolve eq8416 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8416
  have eq8418 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8417
       grind)
    | exact superpose eq8417 eq16
    | exact resolve eq16 eq8417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8419 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8417
       grind)
    | exact superpose eq8417 eq10
    | exact resolve eq10 eq8417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8417
  have eq8476 : x = y := by
    first
    | (have i₁ := eq8419
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8419
    | exact resolve eq8419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8419
  have eq8477 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8418
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq8418
    | exact resolve eq8418 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8418
  have eq8478 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8477
       have i₂ := eq8476
       grind)
    | exact superpose eq8476 eq8477
    | exact resolve eq8477 eq8476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8476 eq8477
  have eq8479 : False := by grind
  exact eq8479

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq60 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq334 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq60 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq12
    | (have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq60 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq359 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq334 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq363 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq359
    | (have j0 := eq359 X0 X1
       grind)
    | exact resolve eq359 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq364 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq363 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq777 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq364
    | exact resolve eq364 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq364 x y
       grind)
    | exact superpose eq364 eq16
    | (have j1 := eq364 x y
       grind)
    | exact resolve eq16 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq809 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq777 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq777
    | (have j0 := eq777 X0 X1
       grind)
    | exact resolve eq777 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq777
  have eq946 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq809 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq809
    | exact resolve eq809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq1167 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq783
       have i₂ := eq946 x y
       grind)
    | exact superpose eq946 eq783
    | (have j1 := eq946 (σ x) (σ y)
       grind)
    | (have r₁ := eq783
       have r₂ := eq946 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq783
       have r₂ := eq946 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq783 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq946
  have eq1170 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1167
  have eq1226 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq10
    | exact resolve eq10 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1262 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1226
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1226
    | exact resolve eq1226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1263 : x = y := by grind
  clear eq1262
  have eq1265 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1263
       grind)
    | exact superpose eq1263 eq16
    | exact resolve eq16 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1266 : False := by grind
  exact eq1266

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pyx_pyy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq44 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq44 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ X0) (σ X1)
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq85 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq85
    | exact resolve eq85 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq85
  have eq97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq186 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq204 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq9
    | exact resolve eq9 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq186
       have i₂ := eq97 y
       grind)
    | exact superpose eq97 eq186
    | exact resolve eq186 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq737 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq690
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq690
    | (have j1 := eq58 y x
       grind)
    | exact resolve eq690 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq690
  have eq738 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq737
  have eq6023 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (M.op (σ y) X0) X0)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq738
       grind)
    | exact superpose eq738 eq9
    | exact resolve eq9 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq6056 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6023 x
       have i₂ := eq204 y x
       grind)
    | exact superpose eq204 eq6023
    | exact resolve eq6023 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq6023
  have eq6066 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6056
       grind)
    | exact superpose eq6056 eq10
    | exact resolve eq10 eq6056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6056
  have eq6117 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6066
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6066
    | exact resolve eq6066 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6066
  have eq6193 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6117
       grind)
    | exact superpose eq6117 eq16
    | exact resolve eq16 eq6117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6117
  have eq6194 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq6193
       have r₂ := eq97 x
       grind)
    | exact resolve eq6193 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6193
  have eq6308 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq6194
       grind)
    | exact superpose eq6194 eq9
    | exact resolve eq9 eq6194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6194
  have eq6345 : x = y := by
    first
    | (have i₁ := eq6308 x
       have i₂ := eq9 x y x
       grind)
    | exact superpose eq9 eq6308
    | exact resolve eq6308 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6308
  have eq6421 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6345
       grind)
    | exact superpose eq6345 eq16
    | exact resolve eq16 eq6345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345
  have eq6423 : False := by grind
  exact eq6423

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_y_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op X0 x) (M.op (M.op x y) y)) = X0 := by
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
  have eq179 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
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
  have eq554 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op (M.op X0 X2) X2)) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq552
       grind)
    | exact superpose eq552 eq40
    | exact resolve eq40 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq586 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq585
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq585
    | exact resolve eq585 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq588 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq586
    | exact resolve eq586 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq554
    | exact resolve eq554 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq596
       have r₂ := eq27
       grind)
    | exact resolve eq596 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq608 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (M.op (σ y) X0) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq603 eq176
    | exact resolve eq176 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq603 eq27
    | exact resolve eq27 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
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
  have eq769 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1809 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq603 eq769
    | (have r₁ := eq769
       have r₂ := eq603
       grind)
    | exact resolve eq769 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq769
  have eq1810 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1809
  have eq1811 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq1810
    | exact resolve eq1810 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810
  have eq1825 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1811 eq182
    | exact resolve eq182 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq1842 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1825
    | exact resolve eq1825 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq1846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq1842
    | exact resolve eq1842 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq1842
  have eq1849 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1846
       have r₂ := eq27
       grind)
    | exact resolve eq1846 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq1850 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1849 eq29
    | exact resolve eq29 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1860 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1849 eq609
    | exact resolve eq609 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq1849
  have eq1861 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq1860
  have eq1871 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1850
    | exact resolve eq1850 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq1875 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq18
    | exact resolve eq18 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1876 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq24
    | exact resolve eq24 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1879 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq175
    | exact resolve eq175 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1881 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq767
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq767
    | (have r₁ := eq767
       have r₂ := eq1871
       grind)
    | exact resolve eq767 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq1871
  have eq1882 : (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq1881
  have eq1885 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1876
    | exact resolve eq1876 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq2259 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq1882
       grind)
    | exact superpose eq1882 eq182
    | exact resolve eq182 eq1882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882
  have eq2268 : (M.op x y) = (k (M.op x y) x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1875 eq2259
    | exact resolve eq2259 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875 eq2259
  have eq2290 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2268 eq40
    | exact resolve eq40 eq2268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2268
  have eq2294 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2290
    | exact resolve eq2290 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2296 : (σ y) = (k (σ y) (σ x)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1885 eq2294
    | exact resolve eq2294 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294
  have eq2317 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2296 eq554
    | exact resolve eq554 eq2296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq2323 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2317
  have eq2335 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2323 eq38
    | exact resolve eq38 eq2323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2341 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2335
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2335
    | exact resolve eq2335 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335
  have eq2343 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1885 eq2341
    | exact resolve eq2341 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341
  have eq2350 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2343 eq554
    | exact resolve eq554 eq2343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq2343
  have eq2355 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2350
  have eq2371 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2355 eq27
    | exact resolve eq27 eq2355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355
  have eq2374 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2371
       have r₂ := eq1885
       grind)
    | exact resolve eq2371 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq2378 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2374 eq27
    | exact resolve eq27 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2379 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ y) X0) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2374 eq176
    | exact resolve eq176 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2380 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2374 eq179
    | exact resolve eq179 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2385 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq2380
    | (have j0 := eq2380 X0
       grind)
    | exact resolve eq2380 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq2386 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2374 eq2385
    | exact resolve eq2385 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374 eq2385
  have eq2854 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1885 eq2378
    | exact resolve eq2378 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378
  have eq2857 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq2854
  have eq2926 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f2926_13 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f2926_14 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) := by
      intro X0
      grind
    have f2926_21 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
      intro X0 X1 X2
      grind
    have f2926_22 : x ≠ (M.op (M.op x y) (M.op x y)) := by grind
    have f2926_24 : x ≠ (M.op x y) := by grind
    have f2926_26 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f2926_14 X0
         grind)
      | (have r₁ := f2926_14 X0
         have r₂ := f2926_24
         grind)
      | exact resolve f2926_14 f2926_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2926_27 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) := by
      intro X0
      first
      | (have j0 := f2926_13 X0
         grind)
      | (have r₁ := f2926_13 X0
         have r₂ := f2926_24
         grind)
      | exact resolve f2926_13 f2926_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2926_32 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f2926_21 X1 X0 (σ x)
         have i₂ := f2926_26 X0
         grind)
      | exact superpose f2926_26 f2926_21
      | exact resolve f2926_21 f2926_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2926_45 : x = (M.op (M.op x y) (M.op x y)) := by
      first
      | (have i₁ := f2926_27 x
         have i₂ := f2926_32 x (M.op x y)
         grind)
      | exact superpose f2926_32 f2926_27
      | exact resolve f2926_27 f2926_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2926_52 : False := by
      first
      | (have r₁ := f2926_45
         have r₂ := f2926_22
         grind)
      | exact resolve f2926_45 f2926_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f2926_52
  clear eq1879 eq2386
  have eq2951 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2926
  have eq2967 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2951 eq28
    | exact resolve eq28 eq2951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951
  have eq2971 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2967
  have eq2982 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2971 eq42
    | exact resolve eq42 eq2971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2971
  have eq2986 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2982
    | exact resolve eq2982 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2982
  have eq2988 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2986
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2986
    | exact resolve eq2986 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq2990 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1885 eq2988
    | exact resolve eq2988 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885 eq2988
  have eq3900 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2990 eq559
    | (have j0 := eq559 (σ y) (σ y) x
       grind)
    | exact resolve eq559 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4026 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2379 eq3900
    | exact resolve eq3900 eq2379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379 eq3900
  have eq4047 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4026
       have r₂ := eq2857
       grind)
    | exact resolve eq4026 eq2857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4026
  have eq4088 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4047 eq182
    | exact resolve eq182 eq4047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4107 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2990 eq4088
    | exact resolve eq4088 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2990 eq4088
  have eq4135 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4107 eq4047
    | exact resolve eq4047 eq4107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047 eq4107
  have eq4158 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq4135
  have eq4170 : x = (M.op x y) := by
    first
    | (have r₁ := eq4158
       have r₂ := eq2857
       grind)
    | exact resolve eq4158 eq2857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857 eq4158
  have eq4182 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4170
       grind)
    | exact superpose eq4170 eq18
    | exact resolve eq18 eq4170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4183 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4170
       grind)
    | exact superpose eq4170 eq22
    | exact resolve eq22 eq4170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4196 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4183 eq20
    | exact resolve eq20 eq4183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4267 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq4182 eq178
    | exact resolve eq178 eq4182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq4285 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4267 X0
       have i₂ := eq4170
       grind)
    | exact superpose eq4170 eq4267
    | exact resolve eq4267 eq4170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4267
  have eq4304 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq4285 eq177
    | exact resolve eq177 eq4285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq4311 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4285 eq608
    | exact resolve eq608 eq4285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq4285
  have eq4649 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4311 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4311
  have eq4688 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4649
       have r₂ := eq1861
       grind)
    | exact resolve eq4649 eq1861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861 eq4649
  have eq4746 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4688 eq116
    | exact resolve eq116 eq4688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq4688
  have eq4763 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq4746
    | exact resolve eq4746 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4746
  have eq4769 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4763
       have i₂ := eq4170
       grind)
    | exact superpose eq4170 eq4763
    | exact resolve eq4763 eq4170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4170 eq4763
  have eq4774 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq559 y y X0
       have i₂ := eq4769
       grind)
    | exact superpose eq4769 eq559
    | (have j0 := eq559 y y x
       grind)
    | exact resolve eq559 eq4769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq4780 : y = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4774 x
       have i₂ := eq4304 y x sF0
       grind)
    | exact superpose eq4304 eq4774
    | exact resolve eq4774 eq4304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4304 eq4774
  have eq4783 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4182 eq4780
    | exact resolve eq4780 eq4182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4780
  have eq4784 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq4783
  have eq4791 : (k y y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq4784
       grind)
    | exact superpose eq4784 eq182
    | exact resolve eq182 eq4784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4809 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4769 eq4791
    | exact resolve eq4791 eq4769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4769 eq4791
  have eq4815 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4784
       have i₂ := eq4809
       grind)
    | exact superpose eq4809 eq4784
    | exact resolve eq4784 eq4809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784 eq4809
  have eq4832 : y = (M.op x y) := by grind
  clear eq4815
  have eq4846 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4832
       grind)
    | exact superpose eq4832 eq24
    | exact resolve eq24 eq4832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq4852 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq4182
       have i₂ := eq4832
       grind)
    | exact superpose eq4832 eq4182
    | exact resolve eq4182 eq4832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4182 eq4832
  have eq4859 : (σ x) = (σ y) := by
    first
    | exact superpose eq4183 eq4846
    | exact resolve eq4846 eq4183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4183 eq4846
  have eq4863 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4859 eq26
    | exact resolve eq26 eq4859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4859
  have eq4955 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4852 eq182
    | exact resolve eq182 eq4852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq4975 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4852 eq4955
    | exact resolve eq4955 eq4852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4852 eq4955
  have eq5057 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4975 eq38
    | exact resolve eq38 eq4975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq4975
  have eq5066 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq5057
    | exact resolve eq5057 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5057
  have eq5068 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4196 eq5066
    | exact resolve eq5066 eq4196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5066
  have eq5080 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5068 eq576
    | (have j0 := eq576 (σ x) (σ x)
       grind)
    | (have r₁ := eq576 (σ x) (σ x)
       have r₂ := eq5068
       grind)
    | exact resolve eq576 eq5068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq5068
  have eq5081 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5080
  have eq5099 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5081 eq4863
    | exact resolve eq4863 eq5081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4863 eq5081
  have eq5140 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5099 eq27
    | exact resolve eq27 eq5099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5099
  have eq5152 : False := by grind
  exact eq5152

/-- `Equation1687`: `x = (y ◇ x) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_pxy_pyx_Equation1687 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1687 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1687.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) y)) := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
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
  have eq55 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 X0
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) (M.op (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq77 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq116 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq38
  have eq147 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : (M.op x x) = (k x (M.op (M.op x y) x)) := by grind
  have eq227 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by grind
  have eq376 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq51 eq67
    | exact resolve eq67 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq52 eq67
    | exact resolve eq67 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (k (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op (M.op X0 X1) X0) X0
       have i₂ := eq14 X0 (M.op (M.op X0 X1) X0) X1
       grind)
    | exact superpose eq14 eq67
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq54 eq67
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq55 eq67
    | exact resolve eq67 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq219 eq67
    | exact resolve eq67 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq387 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq219 eq383
    | exact resolve eq383 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq388 : (σ x) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq55 eq382
    | exact resolve eq382 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq390 : x = (k (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq54 eq380
    | exact resolve eq380 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq391 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq379 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq379
    | exact resolve eq379 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq459 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 (M.op x X0) X1
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq495 : (M.op (M.op x y) x) = (k x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq54 eq391
    | exact resolve eq391 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq496 : (M.op y (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq216 eq391
    | exact resolve eq391 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq497 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq55 eq391
    | exact resolve eq391 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq498 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq219 eq391
    | exact resolve eq391 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq506 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq378 eq498
    | exact resolve eq498 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq498
  have eq507 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq227 eq497
    | exact resolve eq497 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq497
  have eq508 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq376 eq496
    | exact resolve eq496 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq509 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | exact superpose eq225 eq495
    | exact resolve eq495 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq495
  have eq522 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq507 eq388
    | exact resolve eq388 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq507
  have eq671 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq391 X0 x
       have i₂ := eq459 X0 x
       grind)
    | exact superpose eq459 eq391
    | exact resolve eq391 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq459 X0 x
       grind)
    | exact superpose eq459 eq14
    | exact resolve eq14 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq671 X0
       grind)
    | exact superpose eq671 eq68
    | exact resolve eq68 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq838 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq80 X0 X0
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq849 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq838 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq849 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq849 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq849 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq849 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq866 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq856 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq856
    | (have j0 := eq856 X0 X1
       grind)
    | exact resolve eq856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq914 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (M.op (k (M.op X0 X0) X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq674 (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (M.op x (M.op X0 X0))
       have i₂ := eq69 X0 x
       grind)
    | exact superpose eq69 eq674
    | exact resolve eq674 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq914 X0
       have i₂ := eq69 X0 (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq69 eq914
    | exact resolve eq914 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq914
  have eq991 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq987 X0
       have i₂ := eq671 X0
       grind)
    | exact superpose eq671 eq987
    | exact resolve eq987 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq987
  have eq992 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq991 X0
       have i₂ := eq674 X0 X0
       grind)
    | exact superpose eq674 eq991
    | exact resolve eq991 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq7756 : (σ (M.op y (M.op x y))) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) := by
    first
    | exact superpose eq376 eq846
    | (have j0 := eq846 (M.op y (M.op x y)) (M.op x y)
       grind)
    | exact resolve eq846 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7772 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) x))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq390 eq846
    | (have j0 := eq846 x (M.op (M.op x y) x)
       grind)
    | exact resolve eq846 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq7898 : (σ x) = (M.op (σ x) (σ (M.op (M.op x y) x))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by grind
  clear eq7772
  have eq7998 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq509 eq7898
    | exact resolve eq7898 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7898
  have eq8007 : (σ (M.op y (M.op x y))) ≠ (σ (M.op y (M.op x y))) ∨ (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) := by
    first
    | exact superpose eq508 eq7756
    | exact resolve eq7756 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7756
  have eq8008 : (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) := by grind
  clear eq8007
  have eq8108 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7998
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq7998
    | exact resolve eq7998 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7998
  have eq8114 : (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) := by
    first
    | exact superpose eq21 eq8008
    | exact resolve eq8008 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8008
  have eq8201 : (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq8108
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8108
    | exact resolve eq8108 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8108
  have eq8207 : (σ (M.op x y)) = (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) ∨ (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq8114
    | exact resolve eq8114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8114
  have eq8292 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq509 eq8201
    | exact resolve eq8201 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8201
  have eq9533 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op (M.op X0 X1) X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq866 (M.op (M.op X0 X1) X0) X0
       have i₂ := eq391 X0 X1
       grind)
    | exact superpose eq391 eq866
    | (have j0 := eq866 (M.op (M.op X0 X1) X0) X0
       grind)
    | exact resolve eq866 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9708 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X1) X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9533 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9533
  have eq9823 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9708 X0 X1
       have i₂ := eq459 X0 X1
       grind)
    | exact superpose eq459 eq9708
    | (have j0 := eq9708 X0 X1
       grind)
    | exact resolve eq9708 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9708
  have eq9932 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9823 X0 x
       have i₂ := eq459 X0 x
       grind)
    | exact superpose eq459 eq9823
    | (have j0 := eq9823 X0 x
       grind)
    | exact resolve eq9823 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9823
  have eq10349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10349
    | exact resolve eq10349 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10349
  have eq10361 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10350
       have r₂ := eq28
       grind)
    | exact resolve eq10350 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10350
  have eq10363 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10361
    | exact resolve eq10361 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10361
  have eq10377 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10363 eq992
    | exact resolve eq992 eq10363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10363
  have eq10402 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10377
    | exact resolve eq10377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10377
  have eq10403 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10402
  have eq10423 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq992 x
       have i₂ := eq10403
       grind)
    | exact superpose eq10403 eq992
    | exact resolve eq992 eq10403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10403
  have eq10448 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10423
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10423
    | exact resolve eq10423 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10423
  have eq10449 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10448
  have eq10454 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10449 eq28
    | exact resolve eq28 eq10449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10457 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10449 eq117
    | (have r₁ := eq117
       have r₂ := eq10449
       grind)
    | exact resolve eq117 eq10449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq10461 : (σ x) = (k (M.op (σ y) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10449 eq387
    | exact resolve eq387 eq10449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq10464 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10449 eq506
    | exact resolve eq506 eq10449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10449
  have eq10474 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq10457
  have eq16580 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10474 eq102
    | exact resolve eq102 eq10474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10474
  have eq16596 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq16580
  have eq20749 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq16596 eq522
    | exact resolve eq522 eq16596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq16596
  have eq23028 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq20749 eq102
    | exact resolve eq102 eq20749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq20749
  have eq23055 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq23028
  have eq23066 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23055
       have r₂ := eq10454
       grind)
    | exact resolve eq23055 eq10454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10454 eq23055
  have eq23074 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23066 eq10461
    | exact resolve eq10461 eq23066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10461
  have eq23076 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23066 eq10464
    | exact resolve eq10464 eq23066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10464 eq23066
  have eq23211 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq23076
  have eq23213 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq23074
  have eq23807 : (τ (σ x)) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23213 eq147
    | exact resolve eq147 eq23213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq23213
  have eq23833 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq29 eq23807
    | exact resolve eq23807 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23807
  have eq24529 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq992 x
       have i₂ := eq23833
       grind)
    | exact superpose eq23833 eq992
    | exact resolve eq992 eq23833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23833
  have eq24557 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq24529
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24529
    | exact resolve eq24529 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24529
  have eq24558 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq24557
  have eq24566 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24558 eq136
    | exact resolve eq136 eq24558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24579 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24558 eq846
    | (have j0 := eq846 x (M.op x y)
       grind)
    | exact resolve eq846 eq24558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq24581 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24558 eq866
    | (have j0 := eq866 (M.op x y) x
       grind)
    | exact resolve eq866 eq24558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq24558
  have eq24583 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq24581
  have eq24584 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq24579
  have eq24588 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24583
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24583
    | exact resolve eq24583 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24583
  have eq24590 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq24584
    | exact resolve eq24584 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24584
  have eq24599 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24566
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24566
    | exact resolve eq24566 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24566
  have eq24601 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq24588
    | exact resolve eq24588 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24588
  have eq24603 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24590
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24590
    | exact resolve eq24590 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24590
  have eq24605 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24601
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24601
    | exact resolve eq24601 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24601
  have eq24607 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24603
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24603
    | exact resolve eq24603 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24603
  have eq24609 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq24605
    | exact resolve eq24605 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24605
  have eq24611 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq24607
    | exact resolve eq24607 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24607
  have eq26304 : (σ (M.op x y)) = (k (M.op (σ x) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24609 eq391
    | exact resolve eq391 eq24609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq24609
  have eq37881 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24611 eq26304
    | exact resolve eq26304 eq24611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24611 eq26304
  have eq37898 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq37881
  have eq37904 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37898 eq65
    | exact resolve eq65 eq37898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37898
  have eq37935 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq37904
    | exact resolve eq37904 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37904
  have eq38014 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37935 eq758
    | exact resolve eq758 eq37935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758 eq37935
  have eq38108 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38014 eq65
    | exact resolve eq65 eq38014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq38014
  have eq38139 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq38108
    | exact resolve eq38108 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38108
  have eq38140 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq38139
  have eq38154 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38140 eq11
    | (have j0 := eq11 x (M.op x y)
       grind)
    | exact resolve eq11 eq38140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38140
  have eq38165 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq38154
  have eq38173 : (M.op x y) = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq509 eq38165
    | exact resolve eq38165 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq38165
  have eq38189 : (M.op x y) = (M.op x x) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq508 eq38173
    | exact resolve eq38173 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38173
  have eq39120 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq674 x x
       have i₂ := eq38189
       grind)
    | exact superpose eq38189 eq674
    | exact resolve eq674 eq38189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38189
  have eq39136 : x = (M.op y (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq508 eq39120
    | exact resolve eq39120 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39120
  have eq39137 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq39136
  have eq39187 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39137 eq376
    | exact resolve eq376 eq39137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq39196 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39137 eq51
    | exact resolve eq51 eq39137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq39137
  have eq39234 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39196
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq39196
    | exact resolve eq39196 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39196
  have eq39237 : (k (M.op x y) x) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq508 eq39187
    | exact resolve eq39187 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39187
  have eq39240 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq508 eq39234
    | exact resolve eq39234 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39234
  have eq41200 : (k (σ (M.op x y)) (σ x)) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39237 eq136
    | exact resolve eq136 eq39237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq39237
  have eq50694 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39240 eq41200
    | exact resolve eq41200 eq39240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39240 eq41200
  have eq50773 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq50694
  have eq50783 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50773
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq50773
    | exact resolve eq50773 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50773
  have eq51163 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50783 eq24599
    | exact resolve eq24599 eq50783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24599 eq50783
  have eq51210 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq51163
  have eq51234 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51210 eq27
    | exact resolve eq27 eq51210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51210
  have eq52278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51234 eq23211
    | exact resolve eq23211 eq51234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23211 eq51234
  have eq52334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq52278
  have eq52403 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq52334
       have r₂ := eq28
       grind)
    | exact resolve eq52334 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52334
  have eq53292 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq992 x
       have i₂ := eq52403
       grind)
    | exact superpose eq52403 eq992
    | exact resolve eq992 eq52403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52403
  have eq53340 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53292
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53292
    | exact resolve eq53292 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53292
  have eq53341 : x = (M.op x y) := by grind
  clear eq53340
  have eq53352 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq53341 eq21
    | exact resolve eq21 eq53341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq53361 : x ≠ x ∨ y = (M.op x x) ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq53341 eq116
    | (have r₁ := eq116
       have r₂ := eq53341
       grind)
    | exact resolve eq116 eq53341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq53413 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq53341 eq508
    | exact resolve eq508 eq53341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq53444 : y = (M.op x x) ∨ (k y x) = (M.op y x) := by grind
  clear eq53361
  have eq53513 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53352
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53352
    | exact resolve eq53352 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53352
  have eq53516 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq53513 eq27
    | exact resolve eq27 eq53513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74890 : (k y x) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq53444
       have i₂ := eq53413
       grind)
    | exact superpose eq53413 eq53444
    | exact resolve eq53444 eq53413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53444
  have eq74895 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq74890
       grind)
    | exact superpose eq74890 eq77
    | exact resolve eq77 eq74890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq74890
  have eq74937 : (k (σ y) (σ (M.op x y))) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq53513 eq74895
    | exact resolve eq74895 eq53513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74895
  have eq118451 : (σ (M.op x y)) = (M.op (σ (M.op y x)) (σ (M.op y x))) ∨ (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq53341 eq8207
    | exact resolve eq8207 eq53341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8207
  have eq118452 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq118451
       have i₂ := eq53413
       grind)
    | exact superpose eq53413 eq118451
    | exact resolve eq118451 eq53413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118451
  have eq118453 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | exact superpose eq53341 eq118452
    | exact resolve eq118452 eq53341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118452
  have eq118454 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq118453
       have i₂ := eq53413
       grind)
    | exact superpose eq53413 eq118453
    | exact resolve eq118453 eq53413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53413 eq118453
  have eq118487 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq992 (σ (M.op x x))
       have i₂ := eq118454
       grind)
    | exact superpose eq118454 eq992
    | exact resolve eq992 eq118454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118454
  have eq118519 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by grind
  clear eq118487
  have eq118557 : (k (σ y) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq118519
       have i₂ := eq74937
       grind)
    | exact superpose eq74937 eq118519
    | exact resolve eq118519 eq74937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74937 eq118519
  have eq118889 : (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq118557
       have i₂ := eq11 sF3 sF1
       grind)
    | exact superpose eq11 eq118557
    | (have j1 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq118557 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118557
  have eq118937 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq118889
       have i₂ := eq459 sF1 sF3
       grind)
    | exact superpose eq459 eq118889
    | exact resolve eq118889 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq118889
  have eq118941 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq53516 eq118937
    | exact resolve eq118937 eq53516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118937
  have eq118942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq53516 eq118941
    | exact resolve eq118941 eq53516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118941
  have eq118943 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq118942
       have r₂ := eq28
       grind)
    | exact resolve eq118942 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118942
  have eq122738 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq118943 eq674
    | exact resolve eq674 eq118943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq118943
  have eq122764 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq506 eq122738
    | exact resolve eq122738 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122738
  have eq124674 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq122764 eq992
    | exact resolve eq992 eq122764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122764
  have eq124728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq53516 eq124674
    | exact resolve eq124674 eq53516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124674
  have eq124733 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq124728
       have r₂ := eq28
       grind)
    | exact resolve eq124728 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124728
  have eq124754 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq124733 eq52
    | exact resolve eq52 eq124733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq124804 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq53516 eq124754
    | exact resolve eq124754 eq53516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124754
  have eq124812 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq506 eq124804
    | exact resolve eq124804 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq124804
  have eq125575 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq124812 eq124733
    | exact resolve eq124733 eq124812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124733 eq124812
  have eq125604 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq125575
  have eq125629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq8292
       have i₂ := eq125604
       grind)
    | exact superpose eq125604 eq8292
    | exact resolve eq8292 eq125604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8292 eq125604
  have eq125729 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq125629
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq125629
    | exact resolve eq125629 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125629
  have eq125753 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq125729
    | exact resolve eq125729 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq125729
  have eq125767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq53513 eq125753
    | exact resolve eq125753 eq53513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125753
  have eq125773 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq125767
       have r₂ := eq28
       grind)
    | exact resolve eq125767 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125767
  have eq125776 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq53513 eq125773
    | exact resolve eq125773 eq53513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125773
  have eq125779 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq125776
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq125776
    | exact resolve eq125776 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq125776
  have eq126920 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq125779 eq992
    | exact resolve eq992 eq125779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992 eq125779
  have eq126970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq53516 eq126920
    | exact resolve eq126920 eq53516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126920
  have eq126975 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq126970
       have r₂ := eq28
       grind)
    | exact resolve eq126970 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126970
  have eq126979 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq126975 eq30
    | exact resolve eq30 eq126975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq127219 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq126975 eq53516
    | exact resolve eq53516 eq126975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53516 eq126975
  have eq127323 : y = (M.op x y) := by
    first
    | exact superpose eq31 eq126979
    | exact resolve eq126979 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq126979
  have eq127388 : x = y := by
    first
    | exact superpose eq53341 eq127323
    | exact resolve eq127323 eq53341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127323
  have eq128507 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq127388
       grind)
    | exact superpose eq127388 eq19
    | exact resolve eq19 eq127388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq127388
  have eq128819 : x = (M.op x x) := by
    first
    | exact superpose eq53341 eq128507
    | exact resolve eq128507 eq53341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53341 eq128507
  have eq129106 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9932 x
       have i₂ := eq128819
       grind)
    | exact superpose eq128819 eq9932
    | exact resolve eq9932 eq128819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9932 eq128819
  have eq129134 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq129106
  have eq129146 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq129134
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq129134
    | exact resolve eq129134 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq129134
  have eq129167 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq53513 eq129146
    | exact resolve eq129146 eq53513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53513 eq129146
  have eq129183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq127219 eq129167
    | exact resolve eq129167 eq127219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127219 eq129167
  have eq129194 : False := by grind
  exact eq129194
