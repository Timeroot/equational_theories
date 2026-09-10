import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1101`: `x = y ◇ ((x ◇ (z ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyy_pxx_pxy_pyy_Equation1101 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law1101 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1101.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X2)) X1)) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
       have i₂ := eq14 X0 (M.op X0 (M.op X2 X2)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X3 X3))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X3 X3))) X3
       have i₂ := eq14 X0 (M.op X2 (M.op X3 X3)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq61 sF2
       grind)
    | exact superpose eq61 eq49
    | exact resolve eq49 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq61 x
       grind)
    | exact superpose eq61 eq65
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq65
  have eq431 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq50 X1 X3 x
       have i₂ := eq50 X1 X0 x
       grind)
    | (have i₁ := eq50 X1 X1 X1
       have i₂ := eq50 X1 X1 x
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y) X0
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X3 X3) X2
       have i₂ := eq50 (M.op X1 (M.op X2 X2)) X0 X3
       grind)
    | (have i₁ := eq14 X0 (M.op X0 (M.op X0 (M.op X2 X2))) X2
       have i₂ := eq50 X0 (M.op X0 (M.op X2 X2)) X2
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X1 X3 : G, (M.op (M.op X3 X3) X1) = X1 := by
    intro X1 X3
    first
    | (have i₁ := eq451 x X1 x X3
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq451
    | exact resolve eq451 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq463 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq455 X1 (M.op X0 X0)
       grind)
    | exact superpose eq455 eq14
    | exact resolve eq14 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X2 X1) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq463 X0 X2
       grind)
    | (have i₁ := eq12 X2 X1
       have i₂ := eq463 X2 X0
       grind)
    | exact superpose eq463 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq463 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq463 X0 X1
       grind)
    | exact resolve eq12 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (M.op X1 X1) = (M.op X2 X1) := by
    intro X1 X2
    first
    | (have j0 := eq517 x X1 X2
       grind)
    | (have r₁ := eq517 x X1 X2
       have r₂ := eq463 x X1
       grind)
    | (have r₁ := eq517 X1 x X2
       have r₂ := eq463 x X1
       grind)
    | exact resolve eq517 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq517
  have eq567 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X3 X3)) (M.op X0 (M.op X1 X0))) X2) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X2 X3 X1 x
       have i₂ := eq50 X1 X0 x
       grind)
    | (have i₁ := eq51 X0 X1 X1 X1
       have i₂ := eq50 X1 X1 X2
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq1062 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq431 (M.op X1 X2) X2 X3
       have i₂ := eq431 X2 X1 X0
       grind)
    | (have i₁ := eq431 (M.op X1 X2) X2 X3
       have i₂ := eq431 X0 X1 X2
       grind)
    | exact superpose eq431 eq431
    | exact resolve eq431 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq4756 : ∀ X1 X2 : G, (M.op (M.op (M.op y (M.op x y)) (M.op X1 (M.op X2 X1))) x) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq567 X1 X2 x x
       have i₂ := eq434 x
       grind)
    | exact superpose eq434 eq567
    | exact resolve eq567 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq4757 : ∀ X1 X2 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X1 (M.op X2 X1))) (σ x)) = X2 := by
    intro X1 X2
    first
    | exact superpose eq435 eq567
    | exact resolve eq567 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq567
  have eq24943 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op X0 X1))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq4756 sF0 y
       have i₂ := eq1062 X0 X1 sF0 (M.op y sF0)
       grind)
    | (have i₁ := eq4756 X0 y
       have i₂ := eq1062 X0 y sF0 x
       grind)
    | exact superpose eq1062 eq4756
    | exact resolve eq4756 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4756
  have eq24946 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (M.op X0 X1))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq4757 sF4 sF3
       have i₂ := eq1062 X0 X1 sF4 (M.op sF3 sF4)
       grind)
    | (have i₁ := eq4757 X0 sF3
       have i₂ := eq1062 X0 sF3 sF4 x
       grind)
    | exact superpose eq1062 eq4757
    | exact resolve eq4757 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq4757
  have eq487088 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq539 y x
       grind)
    | exact superpose eq539 eq44
    | (have j1 := eq539 y x
       grind)
    | exact resolve eq44 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq487386 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq487088
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq487088
    | exact resolve eq487088 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487088
  have eq487668 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq487386
    | exact resolve eq487386 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487386
  have eq487861 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq487668
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq487668
    | exact resolve eq487668 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487668
  have eq488002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq487861 eq539
    | (have j0 := eq539 (σ y) (σ x)
       grind)
    | exact resolve eq539 eq487861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq487861
  have eq488004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq488002
    | exact resolve eq488002 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488002
  have eq488015 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq488004
       have r₂ := eq27
       grind)
    | exact resolve eq488004 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488004
  have eq488019 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq488015
    | exact resolve eq488015 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488015
  have eq488519 : (σ y) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq488019 eq24946
    | exact resolve eq24946 eq488019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24946 eq488019
  have eq488524 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq488519
       have i₂ := eq455 sF2 (M.op sF3 sF4)
       grind)
    | exact superpose eq455 eq488519
    | exact resolve eq488519 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488519
  have eq489065 : y = (M.op (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24943 y y
       have i₂ := eq488524
       grind)
    | exact superpose eq488524 eq24943
    | exact resolve eq24943 eq488524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24943 eq488524
  have eq489071 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq489065
       have i₂ := eq455 x (M.op y sF0)
       grind)
    | exact superpose eq455 eq489065
    | exact resolve eq489065 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq489065
  have eq489160 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq489071 eq29
    | exact resolve eq29 eq489071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq489071
  have eq489353 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq489160
    | exact resolve eq489160 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq489160
  have eq489354 : x = y := by grind
  clear eq489353
  have eq489380 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq489354
       grind)
    | exact superpose eq489354 eq18
    | exact resolve eq18 eq489354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq489381 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq489354
       grind)
    | exact superpose eq489354 eq24
    | exact resolve eq24 eq489354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq489354
  have eq489727 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq489381
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq489381
    | exact resolve eq489381 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq489381
  have eq489814 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq489727 eq26
    | exact resolve eq26 eq489727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq489727
  have eq490908 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq489814 eq66
    | exact resolve eq66 eq489814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq489814
  have eq491606 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq490908
       have i₂ := eq489380
       grind)
    | exact superpose eq489380 eq490908
    | exact resolve eq490908 eq489380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489380 eq490908
  have eq491966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq491606 eq15
    | exact resolve eq15 eq491606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491606
  have eq492422 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq491966
    | exact resolve eq491966 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq491966
  have eq492556 : False := by grind
  exact eq492556

/-- `Equation1630`: `x = (x ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_y_pyx_pxy_Equation1630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
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
  have eq47 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X0) x)
       have i₂ := eq14 X0 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq62 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq60
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60
    | exact resolve eq60 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq63 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq62
    | exact resolve eq62 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq73 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq73
    | (have j0 := eq73 (σ X0)
       grind)
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq44
    | (have j1 := eq73 x
       grind)
    | exact resolve eq44 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq343 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq81
    | (have j1 := eq73 y
       grind)
    | exact resolve eq81 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq3032 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (σ X0)
       have i₂ := eq338 X0
       grind)
    | exact superpose eq338 eq47
    | (have j1 := eq338 X0
       grind)
    | exact resolve eq47 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3035 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq17925 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op x x) X0)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq63
       grind)
    | exact superpose eq63 eq14
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq17929 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17925 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq17925
    | exact resolve eq17925 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17925
  have eq18119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq17929 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq17929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18119
    | exact resolve eq18119 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18119
  have eq18131 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18120
       have r₂ := eq28
       grind)
    | exact resolve eq18120 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18120
  have eq18136 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq18131 eq14
    | exact resolve eq14 eq18131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18131
  have eq18140 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18136 x
       have i₂ := eq14 sF2 x
       grind)
    | exact superpose eq14 eq18136
    | exact resolve eq18136 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18136
  have eq18146 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  have eq18147 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq18140 eq47
    | exact resolve eq47 eq18140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18140
  have eq18150 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18147
    | exact resolve eq18147 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18147
  have eq18153 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq343
       have i₂ := eq18150
       grind)
    | exact superpose eq18150 eq343
    | exact resolve eq343 eq18150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq18158 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq18150
       grind)
    | exact superpose eq18150 eq47
    | exact resolve eq47 eq18150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18150
  have eq18159 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18153
  have eq18160 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18158
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18158
    | exact resolve eq18158 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18158
  have eq18161 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18159
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18159
    | exact resolve eq18159 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18159
  have eq18162 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18160 eq28
    | exact resolve eq28 eq18160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18160
  have eq18186 : (τ (σ x)) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18161 eq106
    | exact resolve eq106 eq18161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq18209 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq18186
    | exact resolve eq18186 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18186
  have eq18282 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq18146 eq17929
    | exact resolve eq17929 eq18146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17929 eq18146
  have eq18284 : x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq18282
  have eq18492 : y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq18284
       grind)
    | exact superpose eq18284 eq47
    | exact resolve eq47 eq18284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq18284
  have eq18494 : y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18492
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18492
    | exact resolve eq18492 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18492
  have eq18496 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18494
       have r₂ := eq18162
       grind)
    | exact resolve eq18494 eq18162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18162 eq18494
  have eq18498 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18496 eq30
    | exact resolve eq30 eq18496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18496
  have eq18626 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq18498
    | exact resolve eq18498 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18498
  have eq18627 : y = (M.op x y) ∨ x = y := by grind
  clear eq18626
  have eq18628 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq18627 eq21
    | exact resolve eq21 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18753 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18628
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18628
    | exact resolve eq18628 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18628
  have eq19003 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq18753 eq18161
    | exact resolve eq18161 eq18753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18161
  have eq19011 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq19003
  have eq19018 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq19011
       have r₂ := eq28
       grind)
    | exact resolve eq19011 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19011
  have eq68896 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3032 y
       have i₂ := eq18209
       grind)
    | exact superpose eq18209 eq3032
    | (have j0 := eq3032 y
       grind)
    | exact resolve eq3032 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3032 eq18209
  have eq69169 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68896
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq68896
    | exact resolve eq68896 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68896
  have eq69193 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69169
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq69169
    | exact resolve eq69169 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69169
  have eq69209 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq69193
    | exact resolve eq69193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69193
  have eq69210 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq69209
  have eq69216 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq69210
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq69210
    | exact resolve eq69210 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69210
  have eq69220 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq18753 eq69216
    | exact resolve eq69216 eq18753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18753 eq69216
  have eq69240 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq69220
  have eq69242 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq69240
       have r₂ := eq28
       grind)
    | exact resolve eq69240 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69240
  have eq69249 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq69242
  have eq69272 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq69249 eq19018
    | exact resolve eq19018 eq69249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19018 eq69249
  have eq69289 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq69272
  have eq69445 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq69289 eq29
    | exact resolve eq29 eq69289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq69289
  have eq69629 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq69445
    | exact resolve eq69445 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq69445
  have eq69756 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq69629 eq18627
    | exact resolve eq18627 eq69629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18627 eq69629
  have eq69969 : x = y := by grind
  clear eq69756
  have eq70093 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq69969
       grind)
    | exact superpose eq69969 eq19
    | exact resolve eq19 eq69969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq70094 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq69969
       grind)
    | exact superpose eq69969 eq25
    | exact resolve eq25 eq69969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq69969
  have eq70339 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq70094
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq70094
    | exact resolve eq70094 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70094
  have eq70341 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq70339 eq27
    | exact resolve eq27 eq70339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq70339
  have eq70564 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq342
       have i₂ := eq70093
       grind)
    | exact superpose eq70093 eq342
    | exact resolve eq342 eq70093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq70568 : x = (k (M.op x y) x) := by grind
  clear eq70093
  have eq70570 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq70564
    | exact resolve eq70564 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70564
  have eq70576 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq74771 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70570 eq73
    | (have j0 := eq73 (σ x)
       grind)
    | exact resolve eq73 eq70570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq74780 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70341 eq74771
    | exact resolve eq74771 eq70341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74771
  have eq74793 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq74780
       have r₂ := eq28
       grind)
    | exact resolve eq74780 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74780
  have eq74798 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70341 eq74793
    | exact resolve eq74793 eq70341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74793
  have eq74808 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74798 eq70576
    | exact resolve eq70576 eq74798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70576
  have eq74810 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74798 eq28
    | exact resolve eq28 eq74798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74798
  have eq74885 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74808 eq70570
    | exact resolve eq70570 eq74808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70570 eq74808
  have eq74896 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq74885
  have eq74904 : x = (M.op x y) := by
    first
    | (have r₁ := eq74896
       have r₂ := eq74810
       grind)
    | exact resolve eq74896 eq74810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74810 eq74896
  have eq74925 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq74904 eq21
    | exact resolve eq21 eq74904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq75158 : x = (k x x) := by
    first
    | exact superpose eq74904 eq70568
    | exact resolve eq70568 eq74904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70568 eq74904
  have eq75284 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq74925
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq74925
    | exact resolve eq74925 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74925
  have eq75640 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3035 x
       have i₂ := eq75158
       grind)
    | exact superpose eq75158 eq3035
    | (have j0 := eq3035 x
       grind)
    | exact resolve eq3035 eq75158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035 eq75158
  have eq75645 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq75640
  have eq75654 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq75645
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq75645
    | exact resolve eq75645 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq75645
  have eq75673 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70341 eq75654
    | exact resolve eq75654 eq70341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70341 eq75654
  have eq75690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75284 eq75673
    | exact resolve eq75673 eq75284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75284 eq75673
  have eq75706 : False := by grind
  exact eq75706

/-- `Equation1636`: `x = (x ◇ x) ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_pyy_pxx_pxx_pyx_Equation1636 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1636 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1636.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
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
  have eq178 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op (M.op x X0) x)
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) ≠ X0 ∨ (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (k (M.op (M.op X1 X0) X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) X2) (M.op X0 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op (M.op X1 X0) X2) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) ≠ X0 ∨ (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (k (M.op (M.op X1 X0) X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 X2
       have i₂ := eq180 (M.op (M.op X1 X0) X2)
       grind)
    | exact superpose eq180 eq179
    | (have j0 := eq179 X0 X1 X2
       grind)
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq182 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (k (M.op (M.op X1 X0) X2) (k X0 X0)) ∨ (k (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 X1 X2
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq181
    | (have j0 := eq181 X0 X1 X2
       grind)
    | exact resolve eq181 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq183 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) ≠ X0 ∨ (k (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (k (M.op (M.op X1 X0) X2) (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X1 X2
       have i₂ := eq180 (M.op (M.op X1 X0) X2)
       grind)
    | exact superpose eq180 eq182
    | (have j0 := eq182 X0 X1 X2
       grind)
    | exact resolve eq182 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq186 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq186
    | exact resolve eq186 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq190 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq192 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op (k X0 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 x
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq187 X0 X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq187
    | exact resolve eq187 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 : G, (k X0 X0) = (M.op (k (k X0 X0) (k X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq187 (k X0 X0) (M.op X0 x)
       have i₂ := eq187 X0 x
       grind)
    | exact superpose eq187 eq187
    | exact resolve eq187 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : x = (M.op (k x x) (M.op x y)) := by
    first
    | (have i₁ := eq187 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq187
    | (have j0 := eq187 x y
       grind)
    | exact resolve eq187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : (σ x) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq187
    | (have j0 := eq187 (σ x) (σ y)
       grind)
    | exact resolve eq187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq236 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq219 X0
       have i₂ := eq180 (k X0 X0)
       grind)
    | exact superpose eq180 eq219
    | exact resolve eq219 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq240 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq226 eq16
    | exact resolve eq16 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq241 : ∀ X0 : G, (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq240 X0
       have i₂ := eq180 sF0
       grind)
    | exact superpose eq180 eq240
    | exact resolve eq240 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq246 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq227 eq16
    | exact resolve eq16 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq247 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq246 X0
       have i₂ := eq180 sF4
       grind)
    | exact superpose eq180 eq246
    | exact resolve eq246 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq382 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (k x x)) := by
    first
    | (have i₁ := eq241 x
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq241
    | exact resolve eq241 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq387 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq247 sF2
       have i₂ := eq180 sF2
       grind)
    | exact superpose eq180 eq247
    | exact resolve eq247 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq426 : ∀ X0 : G, (k x x) = (M.op (M.op (k x x) (k x x)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq382 eq16
    | exact resolve eq16 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq427 : ∀ X0 : G, (k x x) = (M.op (k (k x x) (k x x)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq426 X0
       have i₂ := eq180 (k x x)
       grind)
    | exact superpose eq180 eq426
    | exact resolve eq426 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq428 : ∀ X0 : G, (k x x) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq427 X0
       have i₂ := eq236 x
       grind)
    | exact superpose eq236 eq427
    | exact resolve eq427 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq431 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq387 eq16
    | exact resolve eq16 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq431 X0
       have i₂ := eq180 (k sF2 sF2)
       grind)
    | exact superpose eq180 eq431
    | exact resolve eq431 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq434 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq432 X0
       have i₂ := eq236 sF2
       grind)
    | exact superpose eq236 eq432
    | exact resolve eq432 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq445 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) X2) (M.op X0 X0)) = X0 ∨ (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op (M.op X1 X0) X2) (M.op X0 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 (M.op (M.op X1 X0) X2) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : (M.op x y) = (k y x) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : (k (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq464
       have i₂ := eq180 sF2
       grind)
    | exact superpose eq180 eq464
    | exact resolve eq464 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq543 : (k x x) = (M.op y y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq461
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq461
    | exact resolve eq461 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq559 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) X2) (k X0 X0)) = X0 ∨ (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq445 X0 X1 X2
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq445
    | (have j0 := eq445 X0 X1 X2
       grind)
    | exact resolve eq445 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq598 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq540
       have i₂ := eq180 sF3
       grind)
    | exact superpose eq180 eq540
    | exact resolve eq540 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq601 : (k x x) = (k y y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq543
       have i₂ := eq180 y
       grind)
    | exact superpose eq180 eq543
    | exact resolve eq543 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq623 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op (M.op X1 X0) X2) (k X0 X0)) = X0 ∨ (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq559 X0 X1 X2
       have i₂ := eq180 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq559
    | (have j0 := eq559 X0 X1 X2
       grind)
    | exact resolve eq559 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq663 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq598
       have i₂ := eq180 sF3
       grind)
    | exact superpose eq180 eq598
    | exact resolve eq598 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq667 : (k x x) = (k y y) ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq601
       have i₂ := eq180 y
       grind)
    | exact superpose eq180 eq601
    | exact resolve eq601 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq683 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (k (k X0 X0) (k X0 X0)) ∨ (k (M.op (M.op X1 X0) X2) (k X0 X0)) = X0 ∨ (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq623 X0 X1 X2
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq623
    | (have j0 := eq623 X0 X1 X2
       grind)
    | exact resolve eq623 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq730 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = X0 ∨ (k (M.op (M.op X1 X0) X2) (k X0 X0)) = X0 ∨ (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq683 X0 X1 X2
       have i₂ := eq236 X0
       grind)
    | exact superpose eq236 eq683
    | (have j0 := eq683 X0 X1 X2
       grind)
    | exact resolve eq683 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq731 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = X0 ∨ (k (M.op (M.op X1 X0) X2) (k X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq730 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq757 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = X0 ∨ (k (M.op (M.op X1 X0) X2) (k X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq731 X0 X1 X2
       have i₂ := eq180 (M.op (M.op X1 X0) X2)
       grind)
    | exact superpose eq180 eq731
    | (have j0 := eq731 X0 X1 X2
       grind)
    | exact resolve eq731 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq731
  have eq1397 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 (k X0 X0) X1
       have i₂ := eq236 X0
       grind)
    | exact superpose eq236 eq193
    | exact resolve eq193 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1463 : (k x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1397 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1397
    | (have j0 := eq1397 x y
       grind)
    | exact resolve eq1397 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1542 : ∀ X0 : G, (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op (k x x) X0)) := by
    intro X0
    first
    | exact superpose eq1463 eq192
    | exact resolve eq192 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq1463
  have eq1741 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1542 (M.op (k x x) x)
       have i₂ := eq193 x x
       grind)
    | exact superpose eq193 eq1542
    | exact resolve eq1542 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq1542
  have eq1991 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  have eq2016 : (M.op x y) ≠ (k x x) ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by grind
  have eq5419 : (k x x) = (M.op (k (k x x) (k x x)) y) ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq225 y
       have i₂ := eq667
       grind)
    | exact superpose eq667 eq225
    | exact resolve eq225 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq5420 : (k (σ x) (σ x)) = (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq663 eq225
    | exact resolve eq225 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq663
  have eq5445 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5420
       have i₂ := eq236 sF2
       grind)
    | exact superpose eq236 eq5420
    | exact resolve eq5420 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5420
  have eq5446 : (M.op x y) = (k x x) ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq5419
       have i₂ := eq236 x
       grind)
    | exact superpose eq236 eq5419
    | exact resolve eq5419 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5419
  have eq5453 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq5445
    | exact resolve eq5445 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5445
  have eq5454 : (M.op x y) = (k x x) ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq5446
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5446
    | exact resolve eq5446 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5446
  have eq5458 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq5453
       have r₂ := eq1991
       grind)
    | exact resolve eq5453 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991 eq5453
  have eq5459 : (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq5454
       have r₂ := eq2016
       grind)
    | exact resolve eq5454 eq2016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016 eq5454
  have eq5473 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq5458 eq190
    | exact resolve eq190 eq5458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5585 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op X1 X0) X2) (k X0 X0)) = X0 ∨ (k (M.op (M.op X1 X0) X2) (k X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X1 X2
       have i₂ := eq757 X0 X1 X2
       grind)
    | exact superpose eq757 eq183
    | (have j1 := eq757 X0 X1 X2
       grind)
    | (have r₁ := eq183 X0 X1 X2
       have r₂ := eq757 X0 X1 X2
       grind)
    | exact resolve eq183 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq757
  have eq5588 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op X1 X0) X2) (k X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq5585 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5585
  have eq5589 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) X2) (k X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq5588 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5588
  have eq5650 : ∀ X0 : G, x = (k (M.op (M.op x y) X0) (k x x)) := by
    intro X0
    first
    | exact superpose eq1741 eq5589
    | exact resolve eq5589 eq1741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741
  have eq5661 : ∀ X0 : G, (k (σ x) (σ x)) = (k (M.op (M.op (σ x) (σ y)) X0) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) := by
    intro X0
    first
    | exact superpose eq387 eq5589
    | exact resolve eq5589 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq5667 : ∀ X0 : G, y = (k (M.op (M.op x y) X0) (k y y)) := by
    intro X0
    first
    | (have i₁ := eq5589 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5589
    | (have j0 := eq5589 y x X0
       grind)
    | exact resolve eq5589 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5589
  have eq5719 : ∀ X0 : G, (k (σ x) (σ x)) = (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq5661 X0
       have i₂ := eq236 sF2
       grind)
    | exact superpose eq236 eq5661
    | exact resolve eq5661 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5661
  have eq6342 : (M.op x y) = (k y x) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq190 y
       have i₂ := eq5459
       grind)
    | exact superpose eq5459 eq190
    | exact resolve eq190 eq5459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq5459
  have eq6456 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq6342
       grind)
    | exact superpose eq6342 eq40
    | exact resolve eq40 eq6342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6342
  have eq6458 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq6456
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6456
    | exact resolve eq6456 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6456
  have eq6460 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq20 eq6458
    | exact resolve eq6458 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6458
  have eq6636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6460 eq5473
    | exact resolve eq5473 eq6460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5473
  have eq6645 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq6636
       have r₂ := eq27
       grind)
    | exact resolve eq6636 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6636
  have eq6656 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6645 eq434
    | exact resolve eq434 eq6645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq6660 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6645 eq5719
    | exact resolve eq5719 eq6645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5719 eq6645
  have eq6682 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6460 eq6660
    | exact resolve eq6660 eq6460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6460 eq6660
  have eq6683 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq26 eq6656
    | exact resolve eq6656 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6656
  have eq6686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6682 eq6683
    | exact resolve eq6683 eq6682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6682 eq6683
  have eq6688 : y = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq6686
       have r₂ := eq27
       grind)
    | exact resolve eq6686 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6686
  have eq6692 : (M.op x y) = (k x x) := by
    first
    | exact superpose eq6688 eq428
    | exact resolve eq428 eq6688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq6707 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq6688 eq1397
    | exact resolve eq1397 eq6688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq6710 : y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6688 eq6707
    | exact resolve eq6707 eq6688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6688 eq6707
  have eq6716 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq6692
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6692
    | exact resolve eq6692 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6692
  have eq6759 : (M.op x y) = (k y y) := by
    first
    | exact superpose eq6710 eq236
    | exact resolve eq236 eq6710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq6710
  have eq6808 : ∀ X0 : G, x = (k (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq5650 X0
       have i₂ := eq6716
       grind)
    | exact superpose eq6716 eq5650
    | exact resolve eq5650 eq6716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5650
  have eq6813 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6716
       grind)
    | exact superpose eq6716 eq40
    | exact resolve eq40 eq6716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq6716
  have eq6841 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6813
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6813
    | exact resolve eq6813 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6813
  have eq6852 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq6841
    | exact resolve eq6841 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6841
  have eq7015 : ∀ X0 : G, y = (k (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq5667 X0
       have i₂ := eq6759
       grind)
    | exact superpose eq6759 eq5667
    | exact resolve eq5667 eq6759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667 eq6759
  have eq7049 : x = y := by
    first
    | exact superpose eq6808 eq7015
    | exact resolve eq7015 eq6808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6808 eq7015
  have eq7059 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq7049
       grind)
    | exact superpose eq7049 eq24
    | exact resolve eq24 eq7049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7049
  have eq7096 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq7059
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7059
    | exact resolve eq7059 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7059
  have eq7144 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq7096 eq5458
    | exact resolve eq5458 eq7096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5458 eq7096
  have eq7161 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq7144
  have eq7167 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6852 eq7161
    | exact resolve eq7161 eq6852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6852 eq7161
  have eq7207 : False := by grind
  exact eq7207

/-- `Equation1636`: `x = (x ◇ x) ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pxx_x_pxy_Equation1636 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1636 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1636.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op y y) (M.op (M.op x y) X0)) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) X2) (M.op X0 X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 (M.op (M.op x X0) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y ≠ (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) ≠ X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X0) (M.op (M.op X1 X0) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X0) (M.op (M.op X1 X0) X2)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op (M.op X1 X0) X2) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) (M.op (M.op X1 X0) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X0 X0) (M.op (M.op X1 X0) X2)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq236 : x = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (σ (k x (k X0 (τ X1)))) = (k (σ x) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq35
    | exact resolve eq35 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq38
  have eq389 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq245 X0
       grind)
    | exact superpose eq245 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq245 X0
       grind)
    | exact resolve eq13 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq395 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq389 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq460 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq49
    | (have j1 := eq75 (σ x)
       grind)
    | exact resolve eq49 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq463 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq28 eq460
    | exact resolve eq460 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq637 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X3)) (M.op (M.op (M.op X1 X0) X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X1 X0) X2) (M.op X0 X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 (M.op X0 X0) X2 x
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X4) (M.op (M.op (M.op X0 X1) X2) X4)) (M.op (M.op X1 X3) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) X2 X3
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op (M.op y X1) (M.op y X1)) (M.op (M.op (M.op x y) X0) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op (M.op (σ y) X1) (M.op (σ y) X1)) (M.op (M.op (M.op (σ x) (σ y)) X0) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq660 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X0 (M.op X0 X1) X2
       have i₂ := eq55 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) X2) = (M.op (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 X2 (M.op (M.op x X0) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op (M.op (M.op X0 x) X1) (M.op (M.op X0 x) X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x X0 X1 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) ≠ X0 ∨ (k (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 X1 X2
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq66
    | (have j0 := eq66 X0 X1 X2
       grind)
    | (have r₁ := eq66 X0 X0 (M.op X0 X1)
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq66 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq740 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X3) ≠ (M.op (M.op (M.op X0 X1) X2) X4) ∨ (M.op X1 X3) = (k (M.op (M.op X1 X3) (M.op X1 X3)) (M.op (M.op (M.op X0 X1) X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq721 (M.op X0 X3) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) X2
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq721
    | (have r₁ := eq721 (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2) (M.op X0 X3)
       have r₂ := eq52 X0 X1 X2 X3
       grind)
    | exact resolve eq721 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq780 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq463 eq395
    | exact resolve eq395 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq806 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X1 X0) X2)) ∨ (M.op (M.op X1 X0) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq74 X0 X1 X2
       grind)
    | (have r₁ := eq74 X1 X1 X2
       have r₂ := eq55 X1 X1
       grind)
    | exact resolve eq74 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq819 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X3) (M.op X1 X3)) = (k (M.op (M.op X1 X3) (M.op X1 X3)) (M.op (M.op (M.op X0 X1) X2) X4)) ∨ (M.op X1 X3) = (M.op (M.op (M.op X0 X1) X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq806 (M.op X0 X3) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) X2
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq806
    | exact resolve eq806 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq851 : (τ (σ x)) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq780 eq49
    | exact resolve eq49 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq780
  have eq852 : x = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq28 eq851
    | exact resolve eq851 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq853 : x = (k x x) := by grind
  clear eq852
  have eq854 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq853
       grind)
    | exact superpose eq853 eq43
    | exact resolve eq43 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq853
  have eq855 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq854
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq854
    | exact resolve eq854 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq893 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq93 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq920 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq893 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq924 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq920 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq920
    | (have j0 := eq920 X0 X1
       grind)
    | exact resolve eq920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq3597 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X0 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq639
    | exact resolve eq639 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3616 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq639 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq639
    | (have j0 := eq639 x X0 y
       grind)
    | exact resolve eq639 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3619 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq639
    | (have j0 := eq639 (σ x) X0 (σ y)
       grind)
    | exact resolve eq639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3659 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3597 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3597
    | (have j0 := eq3597 x y
       grind)
    | exact resolve eq3597 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3662 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq3597
    | (have j0 := eq3597 (σ x) (σ y)
       grind)
    | exact resolve eq3597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3728 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3662 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq3662
       grind)
    | exact resolve eq12 eq3662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3740 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq3728
  have eq3783 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3740 eq395
    | exact resolve eq395 eq3740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740
  have eq3980 : ∀ X0 X1 : G, (M.op y y) = (M.op y (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq642 X0 y X1
       have i₂ := eq55 y y
       grind)
    | exact superpose eq55 eq642
    | exact resolve eq642 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq4026 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 sF3 x
       have i₂ := eq55 sF3 sF3
       grind)
    | exact superpose eq55 eq645
    | exact resolve eq645 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq4081 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq3980 sF0 (M.op (M.op x sF0) x)
       have i₂ := eq14 sF0 x x
       grind)
    | exact superpose eq14 eq3980
    | exact resolve eq3980 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3980
  have eq4126 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op X0 x) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq637 x X0 X1 y X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq637
    | (have j0 := eq637 x X0 X1 y X2
       grind)
    | exact resolve eq637 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4132 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op X0 (σ x)) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq26 eq637
    | (have j0 := eq637 (σ x) X0 X1 (σ y) X2
       grind)
    | exact resolve eq637 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4139 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X1 X0) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq637 X0 X1 X2 X0 X3
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq637
    | exact resolve eq637 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq4238 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y y) X0)) := by
    intro X0
    first
    | exact superpose eq4081 eq14
    | exact resolve eq14 eq4081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4269 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 x) X1) X2) = (M.op (M.op (M.op (M.op (M.op X0 x) X1) X2) (M.op (M.op (M.op X0 x) X1) X2)) (M.op (M.op x y) X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq672 eq52
    | exact resolve eq52 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4470 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4026 sF4 (M.op (M.op x sF4) x)
       have i₂ := eq14 sF4 x x
       grind)
    | exact superpose eq14 eq4026
    | exact resolve eq4026 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4026
  have eq5136 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq50 eq4238
    | exact resolve eq4238 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238
  have eq5871 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq662 X1 (M.op X1 X1) x
       have i₂ := eq55 X1 X1
       grind)
    | exact superpose eq55 eq662
    | exact resolve eq662 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5873 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq662 X2 (M.op (M.op X2 X1) (M.op X2 X1)) X2
       have i₂ := eq639 X2 X1 X2
       grind)
    | exact superpose eq639 eq662
    | exact resolve eq662 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5875 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) (M.op (M.op (M.op X0 X1) X2) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq662 X3 (M.op (M.op (M.op X1 X3) X2) (M.op (M.op X1 X3) X2)) X2
       have i₂ := eq52 X3 X1 X2 X3
       grind)
    | exact superpose eq52 eq662
    | exact resolve eq662 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq5911 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq662 X1 X0 (M.op X0 (M.op X1 X1))
       have i₂ := eq55 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq55 eq662
    | exact resolve eq662 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq7096 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (k (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq917 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq917
    | exact resolve eq917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq7173 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7096 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq7096
    | (have j0 := eq7096 X0 X1
       grind)
    | exact resolve eq7096 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7096
  have eq7213 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7173 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq7173
    | (have j0 := eq7173 X0 X1
       grind)
    | exact resolve eq7173 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7173
  have eq7661 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 x) X1) X2) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 x) X1) X2) X3) (M.op (M.op (M.op (M.op X0 x) X1) X2) X3)) (M.op (M.op (M.op x y) X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq672 eq640
    | exact resolve eq640 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq7740 : ∀ X0 X1 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X3) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq640 X0 X1 (M.op X0 X1) X3 (M.op X0 x) x
       have i₂ := eq639 X0 X1 x
       grind)
    | exact superpose eq639 eq640
    | exact resolve eq640 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7756 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X1 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq640 X0 X1 X2 X3 (M.op (M.op X0 X1) X2) X4
       have i₂ := eq55 (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq55 eq640
    | exact resolve eq640 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq8615 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq740 X0 X1 (M.op X0 X1) x (M.op X0 X2)
       have i₂ := eq639 X0 X1 X2
       grind)
    | exact superpose eq639 eq740
    | (have r₁ := eq740 X1 X1 (M.op X1 X1) X1 (M.op X1 X2)
       have r₂ := eq639 X1 X1 X2
       grind)
    | exact resolve eq740 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq8870 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq924 X0 X1
       have j1 := eq918 X0 X1
       grind)
    | (have r₁ := eq924 X0 X1
       have r₂ := eq918 X0 X1
       grind)
    | (have r₁ := eq924 X0 X0
       have r₂ := eq918 X0 (k X0 X0)
       grind)
    | (have r₁ := eq924 X0 X0
       have r₂ := eq918 X0 X0
       grind)
    | exact resolve eq924 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq924
  have eq8873 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8870 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8870
    | exact resolve eq8870 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9033 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq8870 X0 X1
       grind)
    | exact superpose eq8870 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq8870 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq8870 X0 X1
       grind)
    | exact resolve eq13 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9053 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8870 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8870
  have eq9055 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9033 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq9033 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq9033 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9033
  have eq9101 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8873 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq8873
    | (have j0 := eq8873 X0 X1
       grind)
    | exact resolve eq8873 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8873
  have eq9102 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9055 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq9055
    | (have j0 := eq9055 X0 X1
       grind)
    | exact resolve eq9055 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9055
  have eq9127 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9101 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9101
    | (have j0 := eq9101 X0 X1
       grind)
    | exact resolve eq9101 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq9101
  have eq9318 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X2)) = (k (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq819 X0 X1 (M.op X0 X1) x (M.op X0 X2)
       have i₂ := eq639 X0 X1 X2
       grind)
    | exact superpose eq639 eq819
    | exact resolve eq819 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq819
  have eq14820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14820
    | exact resolve eq14820 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14820
  have eq14832 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14821
       have r₂ := eq27
       grind)
    | exact resolve eq14821 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14821
  have eq14836 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14832
    | exact resolve eq14832 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14832
  have eq14838 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14836
    | exact resolve eq14836 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14836
  have eq14841 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14838 eq73
    | (have r₁ := eq73
       have r₂ := eq14838
       grind)
    | exact resolve eq73 eq14838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq14838
  have eq14887 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq14841
  have eq14888 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq14887
  have eq15214 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14888 eq59
    | exact resolve eq59 eq14888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq15215 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14888 eq110
    | exact resolve eq110 eq14888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14888
  have eq15223 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15215
  have eq15232 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq15214
    | exact resolve eq15214 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15214
  have eq15239 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15232
       have r₂ := eq72
       grind)
    | exact resolve eq15232 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15232
  have eq15242 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq15239
       grind)
    | exact superpose eq15239 eq44
    | exact resolve eq44 eq15239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15239
  have eq15257 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15242
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15242
    | exact resolve eq15242 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15242
  have eq15279 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15257 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq15257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15257
  have eq15282 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15279
    | exact resolve eq15279 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15279
  have eq15293 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15282
    | exact resolve eq15282 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15282
  have eq15297 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15293
    | exact resolve eq15293 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15293
  have eq15298 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15297
  have eq15682 : (M.op x y) = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq395 x
       have i₂ := eq15223
       grind)
    | exact superpose eq15223 eq395
    | exact resolve eq395 eq15223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15223
  have eq15974 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15682 eq45
    | exact resolve eq45 eq15682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq15998 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15974
    | exact resolve eq15974 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15974
  have eq150400 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15682 eq9053
    | (have j0 := eq9053 x (M.op x y)
       grind)
    | exact resolve eq9053 eq15682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15682
  have eq150834 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq150400
  have eq151109 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq150834
    | exact resolve eq150834 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150834
  have eq151492 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq151109
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq151109
    | exact resolve eq151109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151109
  have eq151493 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq151492
  have eq151849 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq151493
    | exact resolve eq151493 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151493
  have eq152139 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq151849
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq151849
    | exact resolve eq151849 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151849
  have eq152465 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq152139 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq152139
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq152139
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq152139
       grind)
    | exact resolve eq13 eq152139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152139
  have eq152503 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq152465
  have eq172427 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq152503 eq15998
    | exact resolve eq15998 eq152503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15998 eq152503
  have eq172470 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq172427
  have eq172516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172470 eq15298
    | exact resolve eq15298 eq172470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298
  have eq172659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq172516
  have eq172703 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq172659
       have r₂ := eq27
       grind)
    | exact resolve eq172659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172659
  have eq172977 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq172703 eq27
    | exact resolve eq27 eq172703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172994 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq172703 eq3662
    | exact resolve eq3662 eq172703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173083 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  have eq173140 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq172994
    | exact resolve eq172994 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172994
  have eq173742 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq173140 eq395
    | exact resolve eq395 eq173140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173140
  have eq174350 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq172703 eq173742
    | exact resolve eq173742 eq172703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172703 eq173742
  have eq174372 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq174350
  have eq174374 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq174372
       have r₂ := eq173083
       grind)
    | exact resolve eq174372 eq173083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174372
  have eq176292 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq174374 eq110
    | exact resolve eq110 eq174374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176399 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq176292
  have eq176416 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq176399
       have r₂ := eq172977
       grind)
    | exact resolve eq176399 eq172977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172977 eq176399
  have eq179134 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq176416
       grind)
    | exact superpose eq176416 eq72
    | (have r₁ := eq72
       have r₂ := eq176416
       grind)
    | exact resolve eq72 eq176416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176416
  have eq179233 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq179134
  have eq179234 : x = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq179233
  have eq182502 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq179234
       grind)
    | exact superpose eq179234 eq44
    | exact resolve eq44 eq179234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179234
  have eq182599 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq182502
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq182502
    | exact resolve eq182502 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182502
  have eq187295 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq182599 eq174374
    | exact resolve eq174374 eq182599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174374 eq182599
  have eq187300 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq187295
  have eq187332 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq187300
       have r₂ := eq173083
       grind)
    | exact resolve eq187300 eq173083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173083 eq187300
  have eq187384 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq187332 eq4470
    | exact resolve eq4470 eq187332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470
  have eq188566 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq187384 eq53
    | exact resolve eq53 eq187384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187384
  have eq190547 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq188566 eq4132
    | exact resolve eq4132 eq188566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4132 eq188566
  have eq199592 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq190547 eq5911
    | exact resolve eq5911 eq190547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190547
  have eq199678 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq187332 eq199592
    | exact resolve eq199592 eq187332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199592
  have eq199843 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq199678
  have eq199850 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq199843
    | exact resolve eq199843 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199843
  have eq199856 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199850 eq237
    | exact resolve eq237 eq199850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq199873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199850 eq172470
    | exact resolve eq172470 eq199850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172470 eq199850
  have eq199984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq199873
  have eq200006 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq199984
       have r₂ := eq27
       grind)
    | exact resolve eq199984 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199984
  have eq200128 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq200006 eq187332
    | exact resolve eq187332 eq200006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200006
  have eq200137 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq200128
  have eq200206 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq200137 eq29
    | exact resolve eq29 eq200137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200218 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq200137 eq110
    | exact resolve eq110 eq200137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq200137
  have eq200701 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq200218
  have eq200785 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq855 eq200701
    | exact resolve eq200701 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq200701
  have eq200786 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq200785
  have eq200796 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq200206
    | exact resolve eq200206 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200206
  have eq200839 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq200796 eq28
    | exact resolve eq28 eq200796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200796
  have eq201475 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq200839
    | exact resolve eq200839 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200839
  have eq201511 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq201475 eq20
    | exact resolve eq20 eq201475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201650 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq201475 eq3659
    | exact resolve eq3659 eq201475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3659
  have eq201965 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq201650
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq201650
    | exact resolve eq201650 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201650
  have eq202086 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq201511
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq201511
    | exact resolve eq201511 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201511
  have eq202791 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq187332 eq199856
    | exact resolve eq199856 eq187332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187332 eq199856
  have eq202938 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq202791
  have eq204061 : (M.op x y) = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq395 x
       have i₂ := eq200786
       grind)
    | exact superpose eq200786 eq395
    | exact resolve eq395 eq200786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200786
  have eq217586 : (M.op x y) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq395 x
       have i₂ := eq201965
       grind)
    | exact superpose eq201965 eq395
    | exact resolve eq395 eq201965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201965
  have eq224805 : y = (k x y) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq201475 eq217586
    | exact resolve eq217586 eq201475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201475 eq217586
  have eq224864 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq224805
  have eq228306 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9053 x y
       have i₂ := eq224864
       grind)
    | exact superpose eq224864 eq9053
    | (have j0 := eq9053 x y
       grind)
    | exact resolve eq9053 eq224864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9053 eq224864
  have eq228310 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq228306
  have eq228329 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq228310
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq228310
    | exact resolve eq228310 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228310
  have eq228349 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq228329
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq228329
    | exact resolve eq228329 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228329
  have eq228357 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq228349
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq228349
    | exact resolve eq228349 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq228349
  have eq228362 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq228357
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq228357
    | exact resolve eq228357 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228357
  have eq228365 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq228362
    | exact resolve eq228362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228362
  have eq229318 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq228365 eq27
    | exact resolve eq27 eq228365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228365
  have eq229462 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq229318
       have r₂ := eq202086
       grind)
    | exact resolve eq229318 eq202086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202086 eq229318
  have eq229465 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq229462 eq29
    | exact resolve eq29 eq229462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq229462
  have eq229925 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq229465
    | exact resolve eq229465 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229465
  have eq229926 : x = (M.op x y) ∨ x = y := by grind
  clear eq229925
  have eq240688 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204061 eq9102
    | exact resolve eq9102 eq204061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9102 eq204061
  have eq241246 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq240688
  have eq241598 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq241246
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq241246
    | exact resolve eq241246 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241246
  have eq242054 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq241598
    | exact resolve eq241598 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241598
  have eq242482 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq242054
    | exact resolve eq242054 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242054
  have eq242682 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq242482
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq242482
    | exact resolve eq242482 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242482
  have eq242683 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq242682
  have eq245429 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq242683 eq202938
    | exact resolve eq202938 eq242683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202938 eq242683
  have eq245544 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq245429
  have eq245592 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq245544 eq28
    | exact resolve eq28 eq245544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq245544
  have eq246331 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq245592
    | exact resolve eq245592 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq245592
  have eq246811 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq246827 : x = (M.op x y) := by
    first
    | (have r₁ := eq246811
       have r₂ := eq229926
       grind)
    | exact resolve eq246811 eq229926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229926 eq246811
  have eq247043 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq246827 eq20
    | exact resolve eq20 eq246827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq247045 : ∀ X0 : G, y = (M.op (M.op y y) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq246827 eq50
    | exact resolve eq50 eq246827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq247047 : x ≠ y ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq246827 eq64
    | exact resolve eq64 eq246827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq247201 : (M.op y y) = (M.op y x) := by
    first
    | exact superpose eq246827 eq4081
    | exact resolve eq4081 eq246827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4081
  have eq247218 : x = (M.op (M.op x x) y) := by
    first
    | exact superpose eq246827 eq5136
    | exact resolve eq5136 eq246827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5136
  have eq247770 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq247043
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq247043
    | exact resolve eq247043 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247043
  have eq247840 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq247770 eq26
    | exact resolve eq26 eq247770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq247909 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq247770 eq3662
    | exact resolve eq3662 eq247770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq247917 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq247770 eq3783
    | exact resolve eq3783 eq247770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3783
  have eq250821 : ∀ X0 X1 : G, x = (M.op (M.op x x) (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7740 (M.op x x) y x x
       have i₂ := eq247218
       grind)
    | exact superpose eq247218 eq7740
    | exact resolve eq7740 eq247218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7740 eq247218
  have eq255458 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) X0)) X0) := by
    intro X0
    first
    | exact superpose eq3619 eq5875
    | exact resolve eq5875 eq3619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3619 eq5875
  have eq255676 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) X0) := by
    intro X0
    first
    | exact superpose eq247770 eq255458
    | exact resolve eq255458 eq247770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255458
  have eq257211 : ∀ X0 : G, y = (M.op (M.op y x) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq247045 X0
       have i₂ := eq247201
       grind)
    | exact superpose eq247201 eq247045
    | exact resolve eq247045 eq247201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247045 eq247201
  have eq257363 : ∀ X1 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op y X1)) := by
    intro X1
    first
    | (have i₁ := eq4126 y (M.op x x) X1
       have i₂ := eq257211 x
       grind)
    | exact superpose eq257211 eq4126
    | exact resolve eq4126 eq257211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4126 eq257211
  have eq257472 : ∀ X1 : G, x = (M.op (M.op x x) (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq246827 eq257363
    | exact resolve eq257363 eq246827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257363
  have eq258733 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5911 (M.op x x) y
       have i₂ := eq257472 y
       grind)
    | exact superpose eq257472 eq5911
    | exact resolve eq5911 eq257472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5911 eq257472
  have eq258801 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq258733
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq258733
    | exact resolve eq258733 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq258733
  have eq258812 : x = (M.op x x) := by
    first
    | exact superpose eq246827 eq258801
    | exact resolve eq258801 eq246827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258801
  have eq258828 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq258812
       grind)
    | exact superpose eq258812 eq72
    | exact resolve eq72 eq258812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq258978 : y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq258828
       have r₂ := eq246331
       grind)
    | exact resolve eq258828 eq246331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246331 eq258828
  have eq258987 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq246827 eq258978
    | exact resolve eq258978 eq246827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258978
  have eq269575 : x = (k x y) ∨ x ≠ y := by
    first
    | (have i₁ := eq247047
       have i₂ := eq258812
       grind)
    | exact superpose eq258812 eq247047
    | exact resolve eq247047 eq258812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247047
  have eq269576 : x = (k x y) := by
    first
    | (have r₁ := eq269575
       have r₂ := eq258987
       grind)
    | exact resolve eq269575 eq258987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258987 eq269575
  have eq269590 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq269576
       grind)
    | exact superpose eq269576 eq44
    | exact resolve eq44 eq269576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq269576
  have eq269670 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq247770 eq269590
    | exact resolve eq269590 eq247770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269590
  have eq269691 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq269670
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq269670
    | exact resolve eq269670 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269670
  have eq269710 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq247770 eq269691
    | exact resolve eq269691 eq247770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269691
  have eq269767 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq269710 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq269710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq247840 eq269767
    | exact resolve eq269767 eq247840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269767
  have eq269788 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq269770
       have r₂ := eq27
       grind)
    | exact resolve eq269770 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269770
  have eq269802 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq247840 eq269788
    | exact resolve eq269788 eq247840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269788
  have eq269815 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq247840 eq269802
    | exact resolve eq269802 eq247840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269802
  have eq269859 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq269815 eq395
    | exact resolve eq395 eq269815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq269815
  have eq270363 : ∀ X0 : G, (M.op x x) = (k (M.op x x) (M.op X0 (M.op x x))) ∨ x = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | exact superpose eq236 eq9318
    | exact resolve eq9318 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq9318
  have eq271494 : ∀ X0 : G, x = (k x (M.op X0 x)) ∨ x = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq270363 X0
       have i₂ := eq258812
       grind)
    | exact superpose eq258812 eq270363
    | (have j0 := eq270363 X0
       grind)
    | exact resolve eq270363 eq258812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270363
  have eq271797 : ∀ X0 : G, x = (k x (M.op X0 x)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq271494 X0
       have i₂ := eq258812
       grind)
    | exact superpose eq258812 eq271494
    | (have j0 := eq271494 X0
       grind)
    | exact resolve eq271494 eq258812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271494
  have eq274723 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 x) X1) X2) = (M.op (M.op (M.op (M.op (M.op X0 x) X1) X2) (M.op (M.op (M.op X0 x) X1) X2)) (M.op x X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq246827 eq4269
    | exact resolve eq4269 eq246827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4269
  have eq275089 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X2 (M.op (M.op (M.op X0 x) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4139 X2 (M.op (M.op X0 x) X1) (M.op (M.op (M.op X0 x) X1) X2) (M.op x x)
       have i₂ := eq274723 X0 X1 X2 x
       grind)
    | exact superpose eq274723 eq4139
    | exact resolve eq4139 eq274723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274723
  have eq286711 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq250821 X0 X1
       have i₂ := eq258812
       grind)
    | exact superpose eq258812 eq250821
    | exact resolve eq250821 eq258812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250821
  have eq286855 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ x = (k (M.op x x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq8615 X0 x (M.op (M.op y X0) x)
       have i₂ := eq286711 X0 x
       grind)
    | exact superpose eq286711 eq8615
    | exact resolve eq8615 eq286711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8615 eq286711
  have eq286865 : ∀ X0 : G, x = (k x (M.op X0 x)) ∨ x ≠ (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq286855 X0
       have i₂ := eq258812
       grind)
    | exact superpose eq258812 eq286855
    | (have j0 := eq286855 X0
       grind)
    | (have r₁ := eq286855 x
       have r₂ := eq258812
       grind)
    | exact resolve eq286855 eq258812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286855
  have eq343389 : ∀ X0 : G, x = (k x (M.op X0 x)) := by
    intro X0
    first
    | (have j0 := eq286865 X0
       have j1 := eq271797 X0
       grind)
    | (have r₁ := eq286865 X0
       have r₂ := eq271797 X0
       grind)
    | exact resolve eq286865 eq271797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271797 eq286865
  have eq345284 : ∀ X0 : G, x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq343389 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq5871 x X0
       grind)
    | exact superpose eq5871 eq343389
    | exact resolve eq343389 eq5871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5871 eq343389
  have eq395038 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq255676 eq4139
    | exact resolve eq4139 eq255676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255676
  have eq395331 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ (M.op x y)) X0) ∨ (M.op X0 X0) = (k X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq395038 eq13
    | (have j0 := eq13 X0 (M.op (σ (M.op x y)) X0)
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq395038 (σ (M.op x y))
       grind)
    | exact resolve eq13 eq395038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395038
  have eq396734 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq275089 (M.op X0 X1) (M.op (M.op X0 X1) x) X0
       have i₂ := eq5873 X0 X1 x
       grind)
    | exact superpose eq5873 eq275089
    | exact resolve eq275089 eq5873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5873 eq275089
  have eq400695 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) x) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq660 X0 (M.op (M.op X0 X1) x) X2
       have i₂ := eq396734 X0 X1
       grind)
    | exact superpose eq396734 eq660
    | exact resolve eq660 eq396734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq396734
  have eq401185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) x) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq400695 X0 X1 X2
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq400695
    | exact resolve eq400695 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400695
  have eq424608 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4139 X1 X0 (M.op X0 X1) (M.op (M.op (M.op (M.op X0 X1) x) x) x)
       have i₂ := eq401185 (M.op X0 X1) x x
       grind)
    | exact superpose eq401185 eq4139
    | exact resolve eq4139 eq401185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139 eq401185
  have eq425089 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq424608 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq424608
    | exact resolve eq424608 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq424608
  have eq583840 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 x) X1) X2) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 x) X1) X2) X3) (M.op (M.op (M.op (M.op X0 x) X1) X2) X3)) (M.op (M.op x X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq246827 eq7661
    | exact resolve eq7661 eq246827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7661 eq246827
  have eq583841 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 x) X1) X2) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 x) X1) X2) X3) (M.op (M.op (M.op X0 x) X1) X2)) (M.op (M.op x X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq583840 X0 X1 X2 X3 X4 X5
       have i₂ := eq425089 (M.op (M.op (M.op X0 x) X1) X2) X3
       grind)
    | exact superpose eq425089 eq583840
    | exact resolve eq583840 eq425089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425089 eq583840
  have eq584223 : ∀ X0 X1 X2 : G, (M.op (M.op x x) X0) = (M.op (M.op (M.op (M.op x x) X0) (M.op x x)) (M.op (M.op x X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3616 eq583841
    | exact resolve eq583841 eq3616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616 eq583841
  have eq584839 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op x X0) x) (M.op (M.op x X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq584223 X0 X1 X2
       have i₂ := eq258812
       grind)
    | exact superpose eq258812 eq584223
    | exact resolve eq584223 eq258812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584223
  have eq1096608 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op x X0) x) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq584839 X0 X0 x
       have i₂ := eq7756 x X0 x X1 X2
       grind)
    | (have i₁ := eq584839 x x x
       have i₂ := eq7756 x x x x x
       grind)
    | exact superpose eq7756 eq584839
    | exact resolve eq584839 eq7756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7756 eq584839
  have eq1192301 : ∀ X0 : G, (M.op x x) ≠ (k (M.op (M.op x x) x) (σ X0)) ∨ (k (M.op (M.op x x) x) (σ X0)) = (M.op (M.op (M.op x x) x) (σ X0)) ∨ (σ X0) = (M.op (M.op (M.op x x) x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7213 (M.op (M.op x x) x) X0
       have i₂ := eq1096608 x x x
       grind)
    | exact superpose eq1096608 eq7213
    | (have j0 := eq7213 (M.op (M.op x x) x) X0
       grind)
    | exact resolve eq7213 eq1096608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7213 eq1096608
  have eq1192537 : ∀ X0 : G, (M.op x x) ≠ (k x (σ X0)) ∨ (k (M.op (M.op x x) x) (σ X0)) = (M.op (M.op (M.op x x) x) (σ X0)) ∨ (σ X0) = (M.op (M.op (M.op x x) x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1192301 X0
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq1192301
    | (have j0 := eq1192301 X0
       grind)
    | exact resolve eq1192301 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192301
  have eq1192910 : ∀ X0 : G, x ≠ (k x (σ X0)) ∨ (k (M.op (M.op x x) x) (σ X0)) = (M.op (M.op (M.op x x) x) (σ X0)) ∨ (σ X0) = (M.op (M.op (M.op x x) x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1192537 X0
       have i₂ := eq258812
       grind)
    | exact superpose eq258812 eq1192537
    | (have j0 := eq1192537 X0
       grind)
    | exact resolve eq1192537 eq258812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192537
  have eq1193042 : ∀ X0 : G, (k x (σ X0)) = (M.op x (σ X0)) ∨ x ≠ (k x (σ X0)) ∨ (σ X0) = (M.op (M.op (M.op x x) x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1192910 X0
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq1192910
    | (have j0 := eq1192910 X0
       grind)
    | exact resolve eq1192910 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192910
  have eq1193089 : ∀ X0 : G, (σ X0) = (M.op x (σ X0)) ∨ (k x (σ X0)) = (M.op x (σ X0)) ∨ x ≠ (k x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1193042 X0
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq1193042
    | (have j0 := eq1193042 X0
       grind)
    | exact resolve eq1193042 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1193042
  have eq1193104 : ∀ X0 : G, (k x (σ X0)) = (M.op x (σ X0)) ∨ (σ X0) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1193089 X0
       have j1 := eq9127 x X0
       grind)
    | (have r₁ := eq1193089 x
       have r₂ := eq9127 x x
       grind)
    | exact resolve eq1193089 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9127 eq1193089
  have eq2783637 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1193104 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1193104
    | exact resolve eq1193104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193104
  have eq2785227 : ∀ X0 : G, (k (σ x) (k (σ x) X0)) = (σ (k x (M.op x (τ X0)))) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq356 x X0
       have i₂ := eq2783637 (τ X0)
       grind)
    | exact superpose eq2783637 eq356
    | (have j1 := eq2783637 (τ X0)
       grind)
    | exact resolve eq356 eq2783637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq2783637
  have eq2786075 : ∀ X0 : G, (σ x) = (k (σ x) (k (σ x) X0)) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2785227 X0
       have i₂ := eq345284 (τ X0)
       grind)
    | exact superpose eq345284 eq2785227
    | (have j0 := eq2785227 X0
       grind)
    | exact resolve eq2785227 eq345284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345284 eq2785227
  have eq2786542 : ∀ X0 : G, (σ x) = (k (σ x) (k (σ x) X0)) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2786075 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2786075
    | (have j0 := eq2786075 X0
       grind)
    | exact resolve eq2786075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786075
  have eq2786846 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | exact superpose eq247770 eq2786542
    | (have j0 := eq2786542 X0
       grind)
    | exact resolve eq2786542 eq247770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786542
  have eq2799219 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq247917 eq2786846
    | (have j0 := eq2786846 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq2786846 eq247917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247917 eq2786846
  have eq2799276 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq2799219
  have eq2800144 : (M.op x x) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2799276 eq3597
    | exact resolve eq3597 eq2799276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3597
  have eq2800377 : x = (M.op x (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2800144
       have i₂ := eq258812
       grind)
    | exact superpose eq258812 eq2800144
    | exact resolve eq2800144 eq258812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258812 eq2800144
  have eq2800462 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2800377 eq2799276
    | exact resolve eq2799276 eq2800377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799276 eq2800377
  have eq2800774 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2800462
  have eq2800890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2800774 eq269859
    | exact resolve eq269859 eq2800774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269859 eq2800774
  have eq2800898 : x = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2800890
       have r₂ := eq27
       grind)
    | exact resolve eq2800890 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2800890
  have eq2800912 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2800898 eq15
    | exact resolve eq15 eq2800898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2800898
  have eq2801563 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2800912
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2800912
    | exact resolve eq2800912 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2800912
  have eq2801631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq247770 eq2801563
    | exact resolve eq2801563 eq247770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247770 eq2801563
  have eq2801677 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2801631
       have r₂ := eq27
       grind)
    | exact resolve eq2801631 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801631
  have eq2801709 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2801677 eq27
    | exact resolve eq27 eq2801677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2801848 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2801677 eq247909
    | exact resolve eq247909 eq2801677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247909
  have eq2802156 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq247840 eq2801848
    | exact resolve eq2801848 eq247840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247840 eq2801848
  have eq2802185 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2801677 eq2802156
    | exact resolve eq2802156 eq2801677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801677 eq2802156
  have eq2802476 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2802185 eq395331
    | exact resolve eq395331 eq2802185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395331 eq2802185
  have eq2802712 : (σ y) = (k (σ (M.op x y)) (σ y)) := by grind
  clear eq2802476
  have eq2802794 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq269710 eq2802712
    | exact resolve eq2802712 eq269710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269710 eq2802712
  have eq2804512 : False := by grind
  exact eq2804512

/-- `Equation1636`: `x = (x ◇ x) ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxx_y_pyx_Equation1636 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1636 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1636.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) X2) (M.op X0 X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 (M.op (M.op x X0) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq54 X0
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108
    | exact resolve eq108 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq242 : (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq69 (M.op x x)
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq69
    | exact resolve eq69 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X0 X0) X2 x
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq516 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq90 X0 X0
       grind)
    | exact superpose eq90 eq54
    | (have j1 := eq90 X0 X0
       grind)
    | exact resolve eq54 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq527 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq516 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq3221 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq370
    | exact resolve eq370 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq3269 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3221 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3221
    | (have j0 := eq3221 x y
       grind)
    | exact resolve eq3221 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3271 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq3221
    | (have j0 := eq3221 (σ x) (σ y)
       grind)
    | exact resolve eq3221 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221
  have eq3521 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq527 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq527
    | exact resolve eq527 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq3618 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3521 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq3521
    | (have j0 := eq3521 X0
       grind)
    | exact resolve eq3521 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3521
  have eq3626 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3618 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3618
    | (have j0 := eq3618 X0
       grind)
    | exact resolve eq3618 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3618
  have eq4430 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq92 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq92
    | (have j0 := eq92 y
       grind)
    | exact resolve eq92 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq4445 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4430
  have eq4448 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4445
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq4445
    | exact resolve eq4445 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq4445
  have eq4470 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4448
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4448 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4448
  have eq4501 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4470 eq89
    | exact resolve eq89 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq14882 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4470 eq105
    | exact resolve eq105 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq4470
  have eq14894 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq14901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14894
    | exact resolve eq14894 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14894
  have eq14912 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq14901
       have r₂ := eq28
       grind)
    | exact resolve eq14901 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14901
  have eq14914 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14912
    | exact resolve eq14912 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14912
  have eq14927 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14914 eq54
    | exact resolve eq54 eq14914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14914
  have eq14952 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14927
    | exact resolve eq14927 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14927
  have eq14953 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14952
  have eq14965 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq14953
       grind)
    | exact superpose eq14953 eq54
    | exact resolve eq54 eq14953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14953
  have eq14989 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14965
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14965
    | exact resolve eq14965 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14965
  have eq14990 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14989
  have eq14993 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14990 eq66
    | (have r₁ := eq66
       have r₂ := eq14990
       grind)
    | exact resolve eq66 eq14990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq15002 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14990 eq3271
    | exact resolve eq3271 eq14990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq15010 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq14993
  have eq15011 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq15002
    | exact resolve eq15002 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15002
  have eq15157 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15011 eq242
    | exact resolve eq242 eq15011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq15011
  have eq15196 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14990 eq15157
    | exact resolve eq15157 eq14990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14990 eq15157
  have eq15233 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15196
  have eq15857 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15233 eq4501
    | exact resolve eq4501 eq15233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15233
  have eq15896 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq15857
    | exact resolve eq15857 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15857
  have eq16176 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3626 y
       have i₂ := eq15896
       grind)
    | exact superpose eq15896 eq3626
    | (have j0 := eq3626 y
       grind)
    | exact resolve eq3626 eq15896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3626 eq15896
  have eq16202 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16176
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16176
    | exact resolve eq16176 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16176
  have eq16203 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq16202
  have eq16438 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq69 y
       have i₂ := eq16203
       grind)
    | exact superpose eq16203 eq69
    | exact resolve eq69 eq16203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq16203
  have eq19996 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15010 eq84
    | exact resolve eq84 eq15010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq15010
  have eq20024 : (k y x) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4501 eq19996
    | exact resolve eq19996 eq4501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4501 eq19996
  have eq20271 : y = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16438
       have i₂ := eq20024
       grind)
    | exact superpose eq20024 eq16438
    | exact resolve eq16438 eq20024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16438 eq20024
  have eq20290 : y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq20271
  have eq20358 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq20290
       grind)
    | exact superpose eq20290 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq20290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20290
  have eq20367 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq20358
  have eq20376 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20367
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20367
    | exact resolve eq20367 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20367
  have eq20377 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq20376
  have eq20403 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq20377
       grind)
    | exact superpose eq20377 eq54
    | exact resolve eq54 eq20377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20377
  have eq20431 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20403
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20403
    | exact resolve eq20403 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20403
  have eq20432 : y = (M.op x y) := by grind
  clear eq20431
  have eq20476 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20432 eq21
    | exact resolve eq21 eq20432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq20545 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20432 eq3269
    | exact resolve eq3269 eq20432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3269
  have eq20560 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20545
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20545
    | exact resolve eq20545 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20545
  have eq20614 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20476
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20476
    | exact resolve eq20476 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20476
  have eq20615 : y = (M.op x x) := by
    first
    | exact superpose eq20432 eq20560
    | exact resolve eq20560 eq20432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20432 eq20560
  have eq20669 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20614 eq27
    | exact resolve eq27 eq20614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq20917 : x = (k y x) := by
    first
    | (have i₁ := eq284 x
       have i₂ := eq20615
       grind)
    | exact superpose eq20615 eq284
    | exact resolve eq284 eq20615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq20923 : x = (M.op y y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq20615
       grind)
    | exact superpose eq20615 eq56
    | exact resolve eq56 eq20615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq20615
  have eq21098 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq20917
       grind)
    | exact superpose eq20917 eq77
    | exact resolve eq77 eq20917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq20917
  have eq21131 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20614 eq21098
    | exact resolve eq21098 eq20614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21098
  have eq21148 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq21131
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21131
    | exact resolve eq21131 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21131
  have eq21355 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21148 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq21148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21148
  have eq21363 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20669 eq21355
    | exact resolve eq21355 eq20669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21355
  have eq21374 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20669 eq21363
    | exact resolve eq21363 eq20669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21363
  have eq21385 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq21374
       have r₂ := eq28
       grind)
    | exact resolve eq21374 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21374
  have eq22590 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21385 eq54
    | exact resolve eq54 eq21385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21385
  have eq22618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20669 eq22590
    | exact resolve eq22590 eq20669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22590
  have eq22624 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22618
       have r₂ := eq28
       grind)
    | exact resolve eq22618 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22618
  have eq22634 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq22624 eq28
    | exact resolve eq28 eq22624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22624
  have eq25060 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14882
       have i₂ := eq20923
       grind)
    | exact superpose eq20923 eq14882
    | exact resolve eq14882 eq20923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14882
  have eq25061 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20614 eq25060
    | exact resolve eq25060 eq20614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25060
  have eq25062 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq25061
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25061
    | exact resolve eq25061 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25061
  have eq25063 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq25062
       have i₂ := eq20923
       grind)
    | exact superpose eq20923 eq25062
    | exact resolve eq25062 eq20923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20923 eq25062
  have eq25076 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq25063 eq54
    | exact resolve eq54 eq25063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq25063
  have eq25105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20669 eq25076
    | exact resolve eq25076 eq20669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20669 eq25076
  have eq25114 : x = y := by
    first
    | (have r₁ := eq25105
       have r₂ := eq28
       grind)
    | exact resolve eq25105 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25105
  have eq25126 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq25114
       grind)
    | exact superpose eq25114 eq25
    | exact resolve eq25 eq25114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq25114
  have eq25291 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20614 eq25126
    | exact resolve eq25126 eq20614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20614 eq25126
  have eq25357 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25291
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25291
    | exact resolve eq25291 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq25291
  have eq25406 : False := by grind
  exact eq25406

/-- `Equation1707`: `x = (y ◇ x) ◇ ((z ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_x_pxy_pyx_pxy_Equation1707 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1707 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1707.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X1) X2)) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X2) = (M.op X0 (M.op (M.op X3 (M.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X1) X2) (M.op X1 X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X2) X0) X3) (M.op X1 (M.op X2 X1))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X0 X2) X0) (M.op X2 X1)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq23
    | exact resolve eq23 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq49 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq15
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq47 (σ X0)
       grind)
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq47 (τ X0)
       grind)
    | exact superpose eq47 eq48
    | exact resolve eq48 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq48
  have eq121 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X2)) = (M.op (M.op X0 X1) (M.op X3 (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq45 (M.op X0 X1) X3 X0 (M.op X2 (M.op X1 X2))
       have i₂ := eq45 X0 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq45 eq45
    | exact resolve eq45 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X2 X3 X4 : G, (M.op X4 (M.op X3 X4)) = (M.op X2 (M.op X3 X2)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq121 x X3 X4 x
       have i₂ := eq121 x X3 X2 x
       grind)
    | (have i₁ := eq121 x x X2 x
       have i₂ := eq121 x x (M.op x x) X3
       grind)
    | exact superpose eq121 eq121
    | exact resolve eq121 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq346 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X1) X0) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq289 X2 (M.op (M.op X0 X1) X0) (M.op X0 X1)
       have i₂ := eq9 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq289
    | exact resolve eq289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X2)) (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq346 (M.op X0 X1) X0 (M.op X2 (M.op X1 X2))
       have i₂ := eq45 X0 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq45 eq346
    | exact resolve eq346 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq910 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq910 X0 X1
       grind)
    | exact superpose eq910 eq15
    | (have j1 := eq910 X0 X1
       grind)
    | exact resolve eq15 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X2 X3) X2)) = (k (σ X0) (σ (M.op (M.op X1 (M.op X3 X0)) X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq912 X0 (M.op (M.op X1 (M.op X3 X0)) X1)
       have i₂ := eq44 X0 X3 X2 X1
       grind)
    | exact superpose eq44 eq912
    | (have j0 := eq912 X0 X1
       grind)
    | exact resolve eq912 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq934 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq912 x y
       grind)
    | exact superpose eq912 eq16
    | (have j1 := eq912 x x
       grind)
    | exact resolve eq16 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq3528 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq934
       have i₂ := eq910 (σ x) (σ y)
       grind)
    | exact superpose eq910 eq934
    | (have j1 := eq910 x x
       grind)
    | (have r₁ := eq934
       have r₂ := eq910 (σ x) (σ y)
       grind)
    | exact resolve eq934 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq3529 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3528
  have eq3577 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq3529
       grind)
    | exact superpose eq3529 eq50
    | exact resolve eq50 eq3529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3529
  have eq3579 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3577
  have eq3631 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq51 (σ x)
       have i₂ := eq3579
       grind)
    | exact superpose eq3579 eq51
    | exact resolve eq51 eq3579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3636 : x = (M.op x x) := by
    first
    | (have i₁ := eq3631
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3631
    | exact resolve eq3631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq3710 : ∀ X0 : G, (M.op (M.op x x) (M.op X0 x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq441 X0 x x
       have i₂ := eq3636
       grind)
    | exact superpose eq3636 eq441
    | exact resolve eq441 eq3636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq3725 : ∀ X0 : G, (M.op x (M.op X0 x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3710 X0
       have i₂ := eq3636
       grind)
    | exact superpose eq3636 eq3710
    | exact resolve eq3710 eq3636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3710
  have eq3769 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3725 (M.op (M.op X0 X1) X0)
       have i₂ := eq346 X0 X1 x
       grind)
    | exact superpose eq346 eq3725
    | exact resolve eq3725 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq3770 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3725 X1
       have i₂ := eq289 X0 X1 x
       grind)
    | (have i₁ := eq3725 X1
       have i₂ := eq289 x X1 X0
       grind)
    | exact superpose eq289 eq3725
    | exact resolve eq3725 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq3725
  have eq5051 : ∀ X0 X2 X3 : G, (σ (M.op (M.op X2 X3) X2)) = (k (σ X0) (σ (M.op X3 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq925 X0 x X2 X3
       have i₂ := eq3769 x (M.op X3 X0)
       grind)
    | exact superpose eq3769 eq925
    | (have j0 := eq925 X0 x X2 X3
       grind)
    | exact resolve eq925 eq3769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq5052 : ∀ X0 X3 : G, (σ X3) = (k (σ X0) (σ (M.op X3 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq5051 X0 x X3
       have i₂ := eq3769 x X3
       grind)
    | exact superpose eq3769 eq5051
    | (have j0 := eq5051 X0 x X3
       grind)
    | exact resolve eq5051 eq3769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5051
  have eq5061 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5052 X0 X1
       have i₂ := eq910 (σ X0) (σ (M.op X1 X0))
       grind)
    | exact superpose eq910 eq5052
    | (have j0 := eq5052 (σ X0) x
       have j1 := eq910 (σ X0) X1
       grind)
    | exact resolve eq5052 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq5052
  have eq10240 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq5061 X0 X1
       grind)
    | exact superpose eq5061 eq51
    | (have j1 := eq5061 X0 X1
       grind)
    | exact resolve eq51 eq5061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq5061
  have eq10264 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10240 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10240
    | (have j0 := eq10240 X0 X1
       grind)
    | exact resolve eq10240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10240
  have eq10265 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (M.op X1 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq10264 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10264
  have eq10299 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3769 (σ X0) (σ (M.op X1 X0))
       have i₂ := eq10265 X0 X1
       grind)
    | exact superpose eq10265 eq3769
    | (have j1 := eq10265 X0 X1
       grind)
    | exact resolve eq3769 eq10265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769 eq10265
  have eq10413 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10299 y x
       grind)
    | exact superpose eq10299 eq16
    | (have j1 := eq10299 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq10299 y x
       grind)
    | exact resolve eq16 eq10299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10299
  have eq10458 : y = (M.op y y) := by grind
  clear eq10413
  have eq10468 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq10458
       grind)
    | exact superpose eq10458 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10458
       grind)
    | exact resolve eq13 eq10458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10469 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq10458
       grind)
    | exact superpose eq10458 eq50
    | exact resolve eq50 eq10458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10458
  have eq10482 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq10468 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10468
  have eq10496 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0
       have i₂ := eq10469
       grind)
    | exact superpose eq10469 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq10469
       grind)
    | exact resolve eq13 eq10469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10469
  have eq10510 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq10496 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10496
  have eq10649 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq10482 X0
       grind)
    | exact superpose eq10482 eq15
    | (have j1 := eq10482 X0
       grind)
    | exact resolve eq15 eq10482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10482
  have eq15395 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10649 x
       grind)
    | exact superpose eq10649 eq16
    | (have j1 := eq10649 x
       grind)
    | exact resolve eq16 eq10649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10649
  have eq15484 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq15395
       have i₂ := eq3636
       grind)
    | exact superpose eq3636 eq15395
    | exact resolve eq15395 eq3636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15395
  have eq15490 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq15484
       have i₂ := eq10510 (σ x)
       grind)
    | exact superpose eq10510 eq15484
    | (have j1 := eq10510 (σ x)
       grind)
    | (have r₁ := eq15484
       have r₂ := eq10510 (σ x)
       grind)
    | exact resolve eq15484 eq10510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10510 eq15484
  have eq15496 : x = (M.op y x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
  clear eq15490
  have eq15498 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq15496
       have i₂ := eq3579
       grind)
    | exact superpose eq3579 eq15496
    | exact resolve eq15496 eq3579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15496
  have eq15506 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3770 x y
       have i₂ := eq15498
       grind)
    | exact superpose eq15498 eq3770
    | exact resolve eq3770 eq15498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15498
  have eq15535 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq15506
       have i₂ := eq3636
       grind)
    | exact superpose eq3636 eq15506
    | exact resolve eq15506 eq3636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3636 eq15506
  have eq15540 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15535
       grind)
    | exact superpose eq15535 eq16
    | exact resolve eq16 eq15535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15535
  have eq15564 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq15540
       have r₂ := eq50 x
       grind)
    | exact resolve eq15540 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15540
  have eq15592 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3770 (σ x) (σ y)
       have i₂ := eq15564
       grind)
    | exact superpose eq15564 eq3770
    | exact resolve eq3770 eq15564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770 eq15564
  have eq15616 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15592
       have i₂ := eq3579
       grind)
    | exact superpose eq3579 eq15592
    | exact resolve eq15592 eq3579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579 eq15592
  have eq15637 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15616
       grind)
    | exact superpose eq15616 eq10
    | exact resolve eq10 eq15616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15616
  have eq15689 : x = y := by
    first
    | (have i₁ := eq15637
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15637
    | exact resolve eq15637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15637
  have eq15691 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15689
       grind)
    | exact superpose eq15689 eq16
    | exact resolve eq16 eq15689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15689
  have eq15712 : False := by grind
  exact eq15712

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq5193 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq5219 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5193
  have eq5220 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5219
  have eq101428 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5220 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5220
    | exact resolve eq5220 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101487 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq5220 X0 X1
       grind)
    | exact superpose eq5220 eq23
    | (have j1 := eq5220 X0 X1
       grind)
    | exact resolve eq23 eq5220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5220
  have eq101707 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101487 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101487
    | (have j0 := eq101487 X0 X1
       grind)
    | exact resolve eq101487 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101487
  have eq101733 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101428 X0 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq101428
    | (have j0 := eq101428 X0 X1
       grind)
    | exact resolve eq101428 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101428
  have eq104181 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (M.op (σ (τ X0)) X1) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq101707 (τ X0) X1
       grind)
    | exact superpose eq101707 eq34
    | (have j1 := eq101707 (τ X0) X1
       grind)
    | exact resolve eq34 eq101707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101707
  have eq104405 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (τ X0) = (τ (k X1 X0)) ∨ (k (τ X0) (τ X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104181 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq104181
    | (have j0 := eq104181 X0 X1
       grind)
    | exact resolve eq104181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104181
  have eq104516 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq104405 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq104405
    | (have j0 := eq104405 X0 X1
       grind)
    | exact resolve eq104405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104405
  have eq104610 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq104516 X0 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq104516
    | (have j0 := eq104516 X0 X1
       grind)
    | exact resolve eq104516 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq104516
  have eq105605 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq104610 X0 X1
       grind)
    | exact superpose eq104610 eq11
    | (have j1 := eq104610 X0 X1
       grind)
    | exact resolve eq11 eq104610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104610
  have eq105852 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105605 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq105605
    | (have j0 := eq105605 X0 X1
       grind)
    | exact resolve eq105605 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105605
  have eq106143 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq101733 X1 X0
       have i₂ := eq105852 X0 X1
       grind)
    | exact superpose eq105852 eq101733
    | (have j0 := eq101733 X1 X0
       have j1 := eq105852 X0 X1
       grind)
    | exact resolve eq101733 eq105852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101733 eq105852
  have eq106413 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq106143 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq106143 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq106143 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq106143 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106143
  have eq106478 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq106413 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq106413 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq106413 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106413
  have eq107174 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ X0)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X0)
       have i₂ := eq106478 X0 X1
       grind)
    | exact superpose eq106478 eq11
    | (have j1 := eq106478 X0 X1
       grind)
    | exact resolve eq11 eq106478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106478
  have eq107423 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq107174 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107174
    | (have j0 := eq107174 X0 X1
       grind)
    | exact resolve eq107174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107174
  have eq107462 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq107423 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq107423 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq107423 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107423
  have eq107665 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq107462 (σ X0) X1
       grind)
    | exact superpose eq107462 eq29
    | (have j1 := eq107462 (σ X0) X1
       grind)
    | exact resolve eq29 eq107462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq107794 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq107462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108854 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq107665 X1 (σ X0)
       grind)
    | exact superpose eq107665 eq23
    | (have j1 := eq107665 X1 (σ X0)
       grind)
    | exact resolve eq23 eq107665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq107665
  have eq108952 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq108854 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq108854
    | (have j0 := eq108854 X0 X1
       grind)
    | exact resolve eq108854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108854
  have eq109058 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq108952 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq108952
    | (have j0 := eq108952 X0 X1
       grind)
    | exact resolve eq108952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108952
  have eq109128 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq109058 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109058
    | (have j0 := eq109058 X0 X1
       grind)
    | exact resolve eq109058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109058
  have eq111073 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq109128 X1 X0
       grind)
    | exact superpose eq109128 eq11
    | (have j1 := eq109128 X1 X0
       grind)
    | exact resolve eq11 eq109128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109128
  have eq112758 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111073 x y
       grind)
    | exact superpose eq111073 eq16
    | (have j1 := eq111073 x y
       grind)
    | exact resolve eq16 eq111073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111073
  have eq113343 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq112758
       have i₂ := eq107462 x y
       grind)
    | exact superpose eq107462 eq112758
    | (have j1 := eq107462 x y
       grind)
    | exact resolve eq112758 eq107462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107462
  have eq113345 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq112758
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq112758
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq112758 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112758
  have eq113348 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq113345
  have eq113349 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq113348
  have eq113352 : y = (M.op x y) ∨ y = (k x y) := by grind
  clear eq113343
  have eq113354 : y = (k x y) := by
    first
    | (have j1 := eq107794 x y
       grind)
    | (have r₁ := eq113352
       have r₂ := eq107794 x y
       grind)
    | exact resolve eq113352 eq107794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107794 eq113352
  have eq114336 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq184 x y
       have i₂ := eq113354
       grind)
    | exact superpose eq113354 eq184
    | (have j0 := eq184 x y
       grind)
    | exact resolve eq184 eq113354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq114357 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq114336
  have eq114364 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq113349
       grind)
    | exact superpose eq113349 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq113349
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq113349
       grind)
    | exact resolve eq12 eq113349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113349
  have eq114404 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq114364
  have eq114406 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq114404
       have i₂ := eq113354
       grind)
    | exact superpose eq113354 eq114404
    | exact resolve eq114404 eq113354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114404
  have eq114407 : y = (M.op x y) := by grind
  clear eq114406
  have eq140412 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq114357
       grind)
    | exact superpose eq114357 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq114357
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq114357
       grind)
    | exact resolve eq12 eq114357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114357
  have eq140456 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq140412
  have eq140496 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140456
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq140456
    | exact resolve eq140456 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140456
  have eq140564 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140496
       have i₂ := eq113354
       grind)
    | exact superpose eq113354 eq140496
    | exact resolve eq140496 eq113354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113354 eq140496
  have eq140565 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq140564
  have eq140606 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140565
       grind)
    | exact superpose eq140565 eq16
    | exact resolve eq16 eq140565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140565
  have eq140738 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq140606
       have i₂ := eq114407
       grind)
    | exact superpose eq114407 eq140606
    | exact resolve eq140606 eq114407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114407 eq140606
  have eq140739 : False := by grind
  exact eq140739

/-- `Equation2602`: `x = (y ◇ ((z ◇ z) ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_pyy_x_pyx_pxy_Equation2602 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2602 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2602.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X2) X0)) X1) = X0 := by
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
  have eq47 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) X0) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X2 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X3 X3) X0))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X3 X3) X0)) X1
       have i₂ := eq14 X0 (M.op (M.op X1 X1) X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq67 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq64
    | exact resolve eq64 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq68 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq67
    | exact resolve eq67 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq98 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq16
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq313 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq364 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq47 X1 X3 x
       have i₂ := eq47 X1 X0 x
       grind)
    | (have i₁ := eq47 X0 X1 X0
       have i₂ := eq47 X0 X0 x
       grind)
    | exact superpose eq47 eq47
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (σ y) (σ x) X0
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) X1) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47 X3 (M.op X3 X1) X2
       have i₂ := eq47 X1 X3 X0
       grind)
    | (have i₁ := eq47 X0 (M.op X2 X2) X2
       have i₂ := eq47 X0 X1 X2
       grind)
    | exact superpose eq47 eq47
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (M.op (M.op X2 X2) X0) x X1
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X0) (M.op X3 X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X3 X3) X1
       have i₂ := eq47 (M.op (M.op X1 X1) X2) X0 X3
       grind)
    | (have i₁ := eq14 X0 (M.op (M.op (M.op X2 X2) X0) X0) X2
       have i₂ := eq47 X0 (M.op (M.op X2 X2) X0) X2
       grind)
    | exact superpose eq47 eq14
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X2 X3 : G, (M.op X2 (M.op X3 X3)) = X2 := by
    intro X2 X3
    first
    | (have i₁ := eq378 x x X2 X3
       have i₂ := eq14 X2 x x
       grind)
    | exact superpose eq14 eq378
    | exact resolve eq378 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq389 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq383 X0 (M.op X1 X1)
       grind)
    | exact superpose eq383 eq14
    | exact resolve eq14 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    grind
  have eq433 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq389 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq389 X0 X1
       grind)
    | exact superpose eq389 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq389 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq389 X0 X0
       grind)
    | exact resolve eq12 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq444 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq77
    | (have j0 := eq77 (σ X0)
       grind)
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq77 sF3
       grind)
    | exact superpose eq77 eq98
    | (have j1 := eq77 (σ y)
       grind)
    | exact resolve eq98 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq98
  have eq462 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X4 X4) X2))) = X1 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq48 X2 x X1 X4
       have i₂ := eq47 X1 X0 x
       grind)
    | (have i₁ := eq48 X0 X0 X0 x
       have i₂ := eq47 X0 X0 X2
       grind)
    | exact superpose eq47 eq48
    | exact resolve eq48 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op X2 X2) X3) (M.op (M.op X0 X1) X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq48 X1 X2 X3 x
       have i₂ := eq47 X1 X0 x
       grind)
    | (have i₁ := eq48 X0 X1 X2 X0
       have i₂ := eq47 X0 X0 X2
       grind)
    | exact superpose eq47 eq48
    | exact resolve eq48 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X3 X3) X4))) = (M.op X0 X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq47 (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X3 X3) X4)) X4 X1
       have i₂ := eq48 X4 X2 X0 X3
       grind)
    | exact superpose eq48 eq47
    | exact resolve eq47 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq48
  have eq516 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (M.op X1 X1)
       have i₂ := eq416 X1 (τ X0)
       grind)
    | exact superpose eq416 eq35
    | exact resolve eq35 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq519 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq516 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq516
    | exact resolve eq516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq905 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq313 X0 (M.op X1 X1)
       have i₂ := eq416 X1 (σ X0)
       grind)
    | exact superpose eq416 eq313
    | exact resolve eq313 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq416
  have eq924 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq905 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq905
    | exact resolve eq905 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq975 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq364 (M.op X2 X1) X2 X3
       have i₂ := eq364 X2 X1 X0
       grind)
    | (have i₁ := eq364 (M.op X2 X1) X2 X3
       have i₂ := eq364 X0 X1 X2
       grind)
    | exact superpose eq364 eq364
    | exact resolve eq364 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq4841 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (σ x) (σ y)) (σ x)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq366 eq462
    | exact resolve eq462 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq5217 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq473 X1 X2 x X1
       have i₂ := eq368 x X1 X0 (M.op X1 X2)
       grind)
    | exact superpose eq368 eq473
    | exact resolve eq473 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq473
  have eq5841 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq444 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq6494 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X3 X3) X1)) (M.op (M.op (M.op X4 X5) X4) (M.op X0 X1))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq462 X4 X5 (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X3 X3) X1)) x
       have i₂ := eq487 X0 x X2 X3 X1
       grind)
    | exact superpose eq487 eq462
    | exact resolve eq462 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq487
  have eq9450 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq519 (σ (M.op X1 X1)) X1
       have i₂ := eq436 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq436 eq519
    | (have j1 := eq436 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq519 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq9464 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq924 (τ (M.op X1 X1)) X1
       have i₂ := eq436 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq436 eq924
    | (have j1 := eq436 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq924 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq924
  have eq9514 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9464 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9464
  have eq9518 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9450 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9450
  have eq9696 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq383 X1 x
       have i₂ := eq9514 x X0
       grind)
    | exact superpose eq9514 eq383
    | exact resolve eq383 eq9514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq9918 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X1) (M.op (σ (M.op X0 X0)) X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq370 X3 X1 x
       have i₂ := eq9518 x X0
       grind)
    | exact superpose eq9518 eq370
    | exact resolve eq370 eq9518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq44915 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4841 sF4 sF2
       have i₂ := eq975 X0 X1 sF4 (M.op sF4 sF2)
       grind)
    | (have i₁ := eq4841 X0 sF2
       have i₂ := eq975 X0 sF2 sF4 x
       grind)
    | exact superpose eq975 eq4841
    | exact resolve eq4841 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq91935 : y = (M.op (σ y) (M.op (M.op (M.op y x) y) (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4841 y y
       have i₂ := eq68
       grind)
    | exact superpose eq68 eq4841
    | exact resolve eq4841 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq91948 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq4841 eq91935
    | exact resolve eq91935 eq4841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4841 eq91935
  have eq463144 : ∀ X0 : G, (M.op X0 X0) = (k y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq453
       have i₂ := eq9514 X0 sF3
       grind)
    | exact superpose eq9514 eq453
    | exact resolve eq453 eq9514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq9514
  have eq470087 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5841 y
       have i₂ := eq463144 X0
       grind)
    | exact superpose eq463144 eq5841
    | (have j0 := eq5841 y
       grind)
    | exact resolve eq5841 eq463144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5841 eq463144
  have eq470115 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq470087 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq470087
    | (have j0 := eq470087 X0
       grind)
    | exact resolve eq470087 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470087
  have eq470481 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq470115 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq470115
    | (have j0 := eq470115 X0
       grind)
    | exact resolve eq470115 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470115
  have eq470482 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq470481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470481
  have eq470679 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq470482 x
       have i₂ := eq9518 X0 x
       grind)
    | exact superpose eq9518 eq470482
    | exact resolve eq470482 eq9518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9518
  have eq1109168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq91948 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq91948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91948
  have eq1109169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq1109168
    | exact resolve eq1109168 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109168
  have eq1109181 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1109169
       have r₂ := eq28
       grind)
    | exact resolve eq1109169 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109169
  have eq1109788 : ∀ X0 X1 X2 X3 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X2 X2) X3)) (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (M.op X1 X3))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1109181 eq6494
    | exact resolve eq6494 eq1109181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109181
  have eq1109824 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f1109824_15 : ∀ X0 X1 X2 X3 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X2 X2) X3)) (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (M.op X1 X3))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = x ∨ y = (M.op x x) := by
      intro X0 X1 X2 X3
      grind
    have f1109824_16 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X3 X3) X1)) (M.op (M.op (M.op X4 X5) X4) (M.op X0 X1))) = X5 := by
      intro X0 X1 X2 X3 X4 X5
      grind
    have f1109824_25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
    have f1109824_26 : (σ y) ≠ (σ x) := by grind
    have f1109824_27 : y ≠ x := by grind
    have f1109824_28 : y ≠ (M.op x x) := by grind
    have f1109824_30 : ∀ X0 X1 X2 X3 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X2 X2) X3)) (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (M.op X1 X3))) ∨ y = x ∨ y = (M.op x x) := by
      intro X0 X1 X2 X3
      first
      | (have j0 := f1109824_15 X0 X1 X2 X3
         grind)
      | (have r₁ := f1109824_15 X0 X1 X2 X3
         have r₂ := f1109824_25
         grind)
      | exact resolve f1109824_15 f1109824_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1109824_31 : ∀ X0 X1 X2 X3 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X2 X2) X3)) (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (M.op X1 X3))) ∨ y = (M.op x x) := by
      intro X0 X1 X2 X3
      first
      | (have j0 := f1109824_30 X0 X1 X2 X3
         grind)
      | (have r₁ := f1109824_30 X0 X1 X2 X3
         have r₂ := f1109824_27
         grind)
      | exact resolve f1109824_30 f1109824_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1109824_32 : ∀ X0 X1 X2 X3 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X2 X2) X3)) (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (M.op X1 X3))) := by
      intro X0 X1 X2 X3
      first
      | (have j0 := f1109824_31 X0 X1 X2 X3
         grind)
      | (have r₁ := f1109824_31 X0 X1 X2 X3
         have r₂ := f1109824_28
         grind)
      | exact resolve f1109824_31 f1109824_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1109824_33 : (σ y) = (σ x) := by
      first
      | (have i₁ := f1109824_32 x x x x
         have i₂ := f1109824_16 x x x x (σ y) (σ x)
         grind)
      | exact superpose f1109824_16 f1109824_32
      | exact resolve f1109824_32 f1109824_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1109824_34 : False := by
      first
      | (have r₁ := f1109824_33
         have r₂ := f1109824_26
         grind)
      | exact resolve f1109824_33 f1109824_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1109824_34
  clear eq6494 eq1109788
  have eq1109937 : ∀ X0 : G, y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1109824
       have i₂ := eq389 sF2 x
       grind)
    | (have i₁ := eq1109824
       have i₂ := eq389 X0 sF2
       grind)
    | exact superpose eq389 eq1109824
    | exact resolve eq1109824 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109824
  have eq1118002 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq470482 x
       have i₂ := eq1109937 X0
       grind)
    | exact superpose eq1109937 eq470482
    | (have j1 := eq1109937 (σ y)
       grind)
    | exact resolve eq470482 eq1109937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470482 eq1109937
  have eq1118176 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq1118002 (σ y)
       grind)
    | (have r₁ := eq1118002 x
       have r₂ := eq470679 (σ y)
       grind)
    | (have r₁ := eq1118002 x
       have r₂ := eq470679 x
       grind)
    | exact resolve eq1118002 eq470679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470679 eq1118002
  have eq1118268 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1118176
       have r₂ := eq25
       grind)
    | exact resolve eq1118176 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118176
  have eq1118621 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1118268 eq9696
    | exact resolve eq9696 eq1118268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9696
  have eq1118894 : (σ x) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1118268 eq44915
    | exact resolve eq44915 eq1118268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44915 eq1118268
  have eq1118902 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1118894
       have i₂ := eq5217 sF3 sF4 sF3
       grind)
    | exact superpose eq5217 eq1118894
    | exact resolve eq1118894 eq5217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5217 eq1118894
  have eq1119068 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30 eq1118621
    | exact resolve eq1118621 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118621
  have eq1119164 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1118902 eq28
    | exact resolve eq28 eq1118902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118902
  have eq1132462 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1119068 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1119068
    | (have j0 := eq1119068 x
       grind)
    | exact resolve eq1119068 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119068
  have eq1134395 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1132462 eq30
    | exact resolve eq30 eq1132462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132462
  have eq1134654 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1134395
    | exact resolve eq1134395 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1134395
  have eq1134655 : x = (M.op x y) ∨ x = y := by grind
  clear eq1134654
  have eq1134656 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1134655 eq21
    | exact resolve eq21 eq1134655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1135103 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1134656
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1134656
    | exact resolve eq1134656 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134656
  have eq1135293 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1135103 eq1119164
    | (have r₁ := eq1119164
       have r₂ := eq1135103
       grind)
    | exact resolve eq1119164 eq1135103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119164 eq1135103
  have eq1135294 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1135293
  have eq1135295 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1135294
  have eq1135369 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1135295 eq30
    | exact resolve eq30 eq1135295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1135295
  have eq1135643 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1135369
    | exact resolve eq1135369 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1135369
  have eq1135910 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1135643 eq1134655
    | exact resolve eq1134655 eq1135643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134655 eq1135643
  have eq1135911 : x = y := by grind
  clear eq1135910
  have eq1136080 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1135911
       grind)
    | exact superpose eq1135911 eq19
    | exact resolve eq19 eq1135911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1136081 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1135911
       grind)
    | exact superpose eq1135911 eq25
    | exact resolve eq25 eq1135911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1135911
  have eq1136491 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1136081
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1136081
    | exact resolve eq1136081 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1136081
  have eq1136493 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1136491 eq27
    | exact resolve eq27 eq1136491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1136491
  have eq1136815 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1136080
       have i₂ := eq389 x X0
       grind)
    | (have i₁ := eq1136080
       have i₂ := eq389 X0 x
       grind)
    | exact superpose eq389 eq1136080
    | exact resolve eq1136080 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq1136080
  have eq1138816 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1136493 eq1136815
    | exact resolve eq1136815 eq1136493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136493
  have eq1139760 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9918 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq1136815 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq1136815 eq9918
    | exact resolve eq9918 eq1136815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9918
  have eq1141067 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq1139760 x
       have i₂ := eq1136815 x
       grind)
    | exact superpose eq1136815 eq1139760
    | exact resolve eq1139760 eq1136815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136815 eq1139760
  have eq1142471 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq1141067
    | exact resolve eq1141067 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1141067
  have eq1143442 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1138816 eq28
    | exact resolve eq28 eq1138816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1138816
  have eq1143872 : False := by grind
  exact eq1143872
