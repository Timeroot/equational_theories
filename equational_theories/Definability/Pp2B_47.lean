import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_y_x_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq60 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq64 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq58 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq58
       grind)
    | exact resolve eq12 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq75 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq72
  have eq76 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq60
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq79 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq76
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq94 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq102 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq166 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq143 eq16
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq395 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq59 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59
    | (have j0 := eq59 y
       grind)
    | exact resolve eq59 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq411 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq508 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X0)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq49
    | (have j0 := eq49 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq49 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq676 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq678 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq677 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq4225 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq678 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq678
    | (have j0 := eq678 (τ X0)
       grind)
    | exact resolve eq678 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq678
  have eq4233 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4225 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4225
    | (have j0 := eq4225 X0
       grind)
    | exact resolve eq4225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4225
  have eq4239 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4233 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4233
    | (have j0 := eq4233 X0
       grind)
    | exact resolve eq4233 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4233
  have eq4409 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) (σ x)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq508 X2 (M.op (M.op (M.op X0 X1) X2) X0)
       have i₂ := eq54 X2 X0 X1
       grind)
    | exact superpose eq54 eq508
    | exact resolve eq508 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq508
  have eq14707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14714 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14707
    | exact resolve eq14707 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14707
  have eq14725 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq14714
       have r₂ := eq28
       grind)
    | exact resolve eq14714 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14714
  have eq14727 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14725
    | exact resolve eq14725 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14725
  have eq14735 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14727 eq51
    | exact resolve eq51 eq14727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14727
  have eq14770 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14735
    | exact resolve eq14735 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14735
  have eq14771 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14770
  have eq15053 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51 y y
       have i₂ := eq14771
       grind)
    | exact superpose eq14771 eq51
    | exact resolve eq51 eq14771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14771
  have eq15088 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15053
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15053
    | exact resolve eq15053 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15053
  have eq15089 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15088
  have eq15090 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15089 eq28
    | exact resolve eq28 eq15089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15097 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15089 eq79
    | exact resolve eq79 eq15089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq15089
  have eq16841 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15097 eq94
    | exact resolve eq94 eq15097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq15097
  have eq16871 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq16841
    | exact resolve eq16841 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16841
  have eq17492 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq16871
  have eq17708 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17492 eq97
    | exact resolve eq97 eq17492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17492
  have eq17728 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq17708
  have eq17738 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq17728
       have r₂ := eq15090
       grind)
    | exact resolve eq17728 eq15090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15090 eq17728
  have eq17743 : x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17738
       have r₂ := eq64
       grind)
    | exact resolve eq17738 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq17738
  have eq17746 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq17743
       grind)
    | exact superpose eq17743 eq45
    | exact resolve eq45 eq17743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq17753 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq17743
       grind)
    | exact superpose eq17743 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq17743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17743
  have eq17760 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq17753
  have eq17768 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17760
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17760
    | exact resolve eq17760 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17760
  have eq17775 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17746
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17746
    | exact resolve eq17746 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17746
  have eq17783 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17768
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17768
    | exact resolve eq17768 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17768
  have eq17943 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17775 eq97
    | exact resolve eq97 eq17775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq17958 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq17943
  have eq17984 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 y y
       have i₂ := eq17783
       grind)
    | exact superpose eq17783 eq51
    | exact resolve eq51 eq17783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17783
  have eq18024 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17984
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17984
    | exact resolve eq17984 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17984
  have eq18025 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18024
  have eq20938 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq51 y y
       have i₂ := eq17958
       grind)
    | exact superpose eq17958 eq51
    | exact resolve eq51 eq17958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17958
  have eq20978 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq20938
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20938
    | exact resolve eq20938 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20938
  have eq20979 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq20978
  have eq21001 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20979 eq102
    | exact resolve eq102 eq20979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq20979
  have eq21130 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq166 eq21001
    | exact resolve eq21001 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq21001
  have eq21547 : (M.op x y) ≠ (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21130 eq4239
    | (have j0 := eq4239 (M.op x y)
       grind)
    | exact resolve eq4239 eq21130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4239 eq21130
  have eq50031 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq75 eq21547
    | exact resolve eq21547 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq21547
  have eq50037 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq50031
       have r₂ := eq18025
       grind)
    | exact resolve eq50031 eq18025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50031
  have eq58817 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq50037
  have eq58821 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq58817
       have r₂ := eq18025
       grind)
    | exact resolve eq58817 eq18025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18025 eq58817
  have eq58876 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58821 eq395
    | exact resolve eq395 eq58821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq58821
  have eq58986 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58876
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58876
    | exact resolve eq58876 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq58876
  have eq58987 : y = (M.op x y) := by grind
  clear eq58986
  have eq58989 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq58987 eq21
    | exact resolve eq21 eq58987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq58987
  have eq59188 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq58989
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq58989
    | exact resolve eq58989 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58989
  have eq59190 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq59188 eq27
    | exact resolve eq27 eq59188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq59302 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59188 eq17775
    | exact resolve eq17775 eq59188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17775
  have eq59623 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) (σ x)) X2)) (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq59188 eq4409
    | exact resolve eq4409 eq59188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4409
  have eq60002 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (M.op X0 X1))) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq59623 X0 X0 (M.op X0 X1)
       have i₂ := eq57 X0 X1 X0
       grind)
    | exact superpose eq57 eq59623
    | exact resolve eq59623 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq59623
  have eq62076 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59302 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq59302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59302
  have eq62088 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59190 eq62076
    | exact resolve eq62076 eq59190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62076
  have eq62103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59190 eq62088
    | exact resolve eq62088 eq59190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62088
  have eq62116 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq62103
       have r₂ := eq28
       grind)
    | exact resolve eq62103 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62103
  have eq67958 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq411 eq60002
    | exact resolve eq60002 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq60002
  have eq68164 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ (M.op x y)))) (σ (M.op x y))) := by
    first
    | exact superpose eq59188 eq67958
    | exact resolve eq67958 eq59188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67958
  have eq89823 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq62116 eq51
    | exact resolve eq51 eq62116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62116
  have eq89919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59190 eq89823
    | exact resolve eq89823 eq59190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89823
  have eq89923 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq89919
       have r₂ := eq28
       grind)
    | exact resolve eq89919 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89919
  have eq90454 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq89923
  have eq90601 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq676 x y
       have i₂ := eq90454
       grind)
    | exact superpose eq90454 eq676
    | (have j0 := eq676 x y
       grind)
    | exact resolve eq676 eq90454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq90454
  have eq90605 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq90601
  have eq90610 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90605
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq90605
    | exact resolve eq90605 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90605
  have eq90628 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59188 eq90610
    | exact resolve eq90610 eq59188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90610
  have eq90646 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90628
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq90628
    | exact resolve eq90628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90628
  have eq90661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59190 eq90646
    | exact resolve eq90646 eq59190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90646
  have eq90667 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq90661
       have r₂ := eq28
       grind)
    | exact resolve eq90661 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90661
  have eq90673 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90667
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq90667
    | exact resolve eq90667 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq90667
  have eq90678 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59188 eq90673
    | exact resolve eq90673 eq59188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59188 eq90673
  have eq90683 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90678
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq90678
    | exact resolve eq90678 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq90678
  have eq90820 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90683 eq51
    | exact resolve eq51 eq90683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90683
  have eq90916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59190 eq90820
    | exact resolve eq90820 eq59190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90820
  have eq90920 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq90916
       have r₂ := eq28
       grind)
    | exact resolve eq90916 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90916
  have eq91005 : (σ (M.op x y)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (σ (M.op x y)))) (σ (M.op x y))) := by
    first
    | exact superpose eq90920 eq68164
    | exact resolve eq68164 eq90920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68164
  have eq91007 : (σ (M.op x y)) = (M.op (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq91005
       have i₂ := eq51 sF2 sF2
       grind)
    | exact superpose eq51 eq91005
    | exact resolve eq91005 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq91005
  have eq91069 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq91007
       have i₂ := eq55 sF2 sF1
       grind)
    | exact superpose eq55 eq91007
    | exact resolve eq91007 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq91007
  have eq91094 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq59190 eq91069
    | exact resolve eq91069 eq59190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91069
  have eq91099 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq90920 eq91094
    | exact resolve eq91094 eq90920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90920 eq91094
  have eq91100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59190 eq91099
    | exact resolve eq91099 eq59190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59190 eq91099
  have eq91101 : False := by grind
  exact eq91101

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq22
    | exact resolve eq22 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq38 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq46 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq24 (τ X0) (τ X0)
       grind)
    | exact superpose eq24 eq38
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq43
    | exact resolve eq43 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq98 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq26 X1 X2 X0
       grind)
    | exact superpose eq26 eq22
    | exact resolve eq22 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 x x
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq72
  have eq186 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq188 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq186
    | (have j0 := eq186 X0
       grind)
    | exact resolve eq186 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq524 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq46 x
       have i₂ := eq74 (τ x) x
       grind)
    | exact superpose eq74 eq46
    | (have j1 := eq74 (τ X0) X0
       grind)
    | exact resolve eq46 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq537 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (M.op X1 (τ X0)) X2
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq43
    | (have j1 := eq74 X1 X0
       grind)
    | exact resolve eq43 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq74
  have eq543 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq524 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq544 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq537 X0 X1 X2
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq537
    | (have j0 := eq537 X0 X1 X2
       grind)
    | exact resolve eq537 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq537
  have eq549 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq543 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq543
    | (have j0 := eq543 X0
       grind)
    | exact resolve eq543 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq661 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) = (σ (k (τ (k X0 X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq188 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq188
    | (have j0 := eq188 (τ X0)
       grind)
    | exact resolve eq188 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq678 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) = (k (σ (τ (k X0 X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq661 X0
       have i₂ := eq19 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq19 eq661
    | (have j0 := eq661 X0
       grind)
    | exact resolve eq661 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq661
  have eq686 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (σ (τ X0)) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq678 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq678
    | (have j0 := eq678 X0
       grind)
    | exact resolve eq678 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq691 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq686 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq686
    | (have j0 := eq686 X0
       grind)
    | exact resolve eq686 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq695 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq691 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq691
    | (have j0 := eq691 X0
       grind)
    | exact resolve eq691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq1266 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (k (σ X0) (σ X0)) X0
       have i₂ := eq549 (σ X0)
       grind)
    | exact superpose eq549 eq36
    | (have j1 := eq549 (σ X0)
       grind)
    | exact resolve eq36 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq1274 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1266 x
       have i₂ := eq36 (σ x) x
       grind)
    | exact superpose eq36 eq1266
    | (have j0 := eq1266 X0
       grind)
    | exact resolve eq1266 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq1290 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1274 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1274
    | (have j0 := eq1274 X0
       grind)
    | exact resolve eq1274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1304 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1290 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1290
    | (have j0 := eq1290 X0
       grind)
    | exact resolve eq1290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1336 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq695 X0
       have i₂ := eq1304 X0
       grind)
    | exact superpose eq1304 eq695
    | (have j0 := eq695 X0
       have j1 := eq1304 X0
       grind)
    | exact resolve eq695 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq1347 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1336 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1391 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq172
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq172
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq172 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1392 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1391
  have eq1402 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 (k X0 X0) X1
       have i₂ := eq1347 X0
       grind)
    | exact superpose eq1347 eq26
    | (have j1 := eq1347 X0
       grind)
    | exact resolve eq26 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq1796 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X0 X0 X0
       have i₂ := eq1402 X0 X1
       grind)
    | exact superpose eq1402 eq98
    | (have j1 := eq1402 X0 X2
       grind)
    | exact resolve eq98 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1402
  have eq1835 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1796 X0 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq1796
    | (have j0 := eq1796 X0 X1 X2
       grind)
    | exact resolve eq1796 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq2057 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1835 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq2058 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2057 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2133 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq2058 X0
       grind)
    | exact superpose eq2058 eq9
    | exact resolve eq9 eq2058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2135 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k X0 X0) X0 X0
       have i₂ := eq2058 X0
       grind)
    | exact superpose eq2058 eq23
    | exact resolve eq23 eq2058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2058
  have eq2183 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2135 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2135
    | exact resolve eq2135 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135
  have eq2280 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2133 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2133
    | exact resolve eq2133 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2345 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ (k X0 X0)) (σ X0) X1
       have i₂ := eq2183 X0
       grind)
    | exact superpose eq2183 eq26
    | exact resolve eq26 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183
  have eq20491 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1304 (τ X0)
       have i₂ := eq544 X0 (τ X0) X0
       grind)
    | exact superpose eq544 eq1304
    | (have j0 := eq1304 (τ X0)
       have j1 := eq544 X0 (τ X0) x
       grind)
    | exact resolve eq1304 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq1304
  have eq20553 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20491 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20491
  have eq20600 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq20553 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq20553
    | (have j0 := eq20553 X0
       grind)
    | exact resolve eq20553 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20553
  have eq20635 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq20600
  have eq20652 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20635 X0
       have i₂ := eq24 (τ X0) (τ X0)
       grind)
    | exact superpose eq24 eq20635
    | (have j0 := eq20635 X0
       grind)
    | exact resolve eq20635 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20635
  have eq23270 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1392
  have eq23587 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq20652
  have eq23690 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23587 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq23587
    | (have j0 := eq23587 X0
       grind)
    | exact resolve eq23587 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq23587
  have eq23691 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq23690 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23690
  have eq24672 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23691 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23691
    | exact resolve eq23691 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23691
  have eq24844 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq24672 X0
       have i₂ := eq36 (σ X0) X0
       grind)
    | exact superpose eq36 eq24672
    | exact resolve eq24672 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq24672
  have eq24877 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq24844 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24844
    | exact resolve eq24844 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24844
  have eq24947 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2280 X0
       have i₂ := eq24877 X0
       grind)
    | exact superpose eq24877 eq2280
    | exact resolve eq2280 eq24877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280
  have eq24952 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2345 X0 X1
       have i₂ := eq24877 X0
       grind)
    | exact superpose eq24877 eq2345
    | exact resolve eq2345 eq24877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345
  have eq25032 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq24877 (σ X0)
       grind)
    | exact superpose eq24877 eq15
    | exact resolve eq15 eq24877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25093 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25032 X0
       have i₂ := eq24877 X0
       grind)
    | exact superpose eq24877 eq25032
    | exact resolve eq25032 eq24877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24877 eq25032
  have eq1293861 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq172
       have i₂ := eq23270
       grind)
    | exact superpose eq23270 eq172
    | exact resolve eq172 eq23270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq23270
  have eq1293923 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1293861
  have eq1293924 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1293923
  have eq1293961 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1293924
       have i₂ := eq25093 x
       grind)
    | exact superpose eq25093 eq1293924
    | exact resolve eq1293924 eq25093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293924
  have eq1293987 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1293961
       have i₂ := eq25093 x
       grind)
    | exact superpose eq25093 eq1293961
    | exact resolve eq1293961 eq25093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25093 eq1293961
  have eq1294070 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1293987
       grind)
    | exact superpose eq1293987 eq10
    | exact resolve eq10 eq1293987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293987
  have eq1294712 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1294070
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1294070
    | exact resolve eq1294070 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294070
  have eq1295146 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1294712
       grind)
    | exact superpose eq1294712 eq10
    | exact resolve eq10 eq1294712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294712
  have eq1295794 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1295146
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1295146
    | exact resolve eq1295146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295146
  have eq1295795 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq1295794
  have eq1295964 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24947 x
       have i₂ := eq1295795
       grind)
    | exact superpose eq1295795 eq24947
    | exact resolve eq24947 eq1295795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24947
  have eq1296363 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq1295795
       grind)
    | exact superpose eq1295795 eq24
    | exact resolve eq24 eq1295795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1295795
  have eq1317818 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1295964
       grind)
    | exact superpose eq1295964 eq16
    | exact resolve eq16 eq1295964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295964
  have eq1318341 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1317818
       have i₂ := eq1296363
       grind)
    | exact superpose eq1296363 eq1317818
    | exact resolve eq1317818 eq1296363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296363 eq1317818
  have eq1318346 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by grind
  clear eq1318341
  have eq1318347 : x = (M.op x x) := by grind
  clear eq1318346
  have eq1319988 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24952 x X0
       have i₂ := eq1318347
       grind)
    | exact superpose eq1318347 eq24952
    | exact resolve eq24952 eq1318347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24952
  have eq1320330 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 x x X0
       have i₂ := eq1318347
       grind)
    | exact superpose eq1318347 eq26
    | exact resolve eq26 eq1318347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1318347
  have eq1320790 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1320330 X0
       have i₂ := eq22 x X0
       grind)
    | exact superpose eq22 eq1320330
    | exact resolve eq1320330 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320330
  have eq1321083 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1319988 X0
       have i₂ := eq22 (σ x) X0
       grind)
    | exact superpose eq22 eq1319988
    | exact resolve eq1319988 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1319988
  have eq1330400 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1321083 (σ y)
       grind)
    | exact superpose eq1321083 eq16
    | exact resolve eq16 eq1321083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321083
  have eq1331477 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1330400
       have i₂ := eq1320790 y
       grind)
    | exact superpose eq1320790 eq1330400
    | exact resolve eq1330400 eq1320790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320790 eq1330400
  have eq1331478 : False := by grind
  exact eq1331478

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 X1) X0
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq109 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq111 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  clear eq19
  have eq739 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq97
  have eq741 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq739 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq739
    | (have j0 := eq739 X0
       grind)
    | exact resolve eq739 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq742 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq741 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq763 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109 x y
       grind)
    | exact superpose eq109 eq16
    | (have j1 := eq109 x y
       grind)
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq797 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq763
       have i₂ := eq742 x
       grind)
    | exact superpose eq742 eq763
    | exact resolve eq763 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq800 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
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
  have eq808 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq65 (σ X0) (σ X0)
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq65
    | exact resolve eq65 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq800 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq800
    | exact resolve eq800 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq800
  have eq830 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq828 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq828
    | exact resolve eq828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq975 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq808 X0
       have i₂ := eq830 X0
       grind)
    | exact superpose eq830 eq808
    | exact resolve eq808 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq1072 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq65 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq975 X0
       grind)
    | exact superpose eq975 eq65
    | exact resolve eq65 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq975
  have eq13453 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq111
    | exact resolve eq111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq13710 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13453 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13453
    | (have j0 := eq13453 X0 X1
       grind)
    | exact resolve eq13453 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13453
  have eq22271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq797
       have i₂ := eq13710 y x
       grind)
    | exact superpose eq13710 eq797
    | (have j1 := eq13710 (σ y) (σ (k x x))
       grind)
    | (have r₁ := eq797
       have r₂ := eq13710 y x
       grind)
    | (have r₁ := eq797
       have r₂ := eq13710 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq797
       have r₂ := eq13710 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq797 eq13710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797 eq13710
  have eq22272 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq22271
  have eq22274 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22272
       have i₂ := eq830 x
       grind)
    | exact superpose eq830 eq22272
    | exact resolve eq22272 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22272
  have eq22276 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22274
       grind)
    | exact superpose eq22274 eq16
    | exact resolve eq16 eq22274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22274
  have eq22277 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22276
       have i₂ := eq742 x
       grind)
    | exact superpose eq742 eq22276
    | exact resolve eq22276 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22276
  have eq22278 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22277
       have i₂ := eq830 x
       grind)
    | exact superpose eq830 eq22277
    | exact resolve eq22277 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22277
  have eq22279 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq22278
  have eq22281 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22279
       grind)
    | exact superpose eq22279 eq10
    | exact resolve eq10 eq22279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22279
  have eq22402 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22281
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22281
    | exact resolve eq22281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22281
  have eq22420 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22402
       grind)
    | exact superpose eq22402 eq16
    | exact resolve eq16 eq22402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22402
  have eq22421 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22420
       have i₂ := eq742 x
       grind)
    | exact superpose eq742 eq22420
    | exact resolve eq22420 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq22420
  have eq22422 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22421
       have i₂ := eq830 x
       grind)
    | exact superpose eq830 eq22421
    | exact resolve eq22421 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq22421
  have eq22423 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq22422
  have eq22455 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq22423
       grind)
    | exact superpose eq22423 eq10
    | exact resolve eq10 eq22423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22423
  have eq22576 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22455
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq22455
    | exact resolve eq22455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22455
  have eq22577 : y = (M.op x x) := by grind
  clear eq22576
  have eq22604 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1072 x
       have i₂ := eq22577
       grind)
    | exact superpose eq22577 eq1072
    | exact resolve eq1072 eq22577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq22667 : y = (M.op x y) := by
    first
    | (have i₁ := eq67 x x
       have i₂ := eq22577
       grind)
    | exact superpose eq22577 eq67
    | exact resolve eq67 eq22577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq22577
  have eq23092 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22604
       grind)
    | exact superpose eq22604 eq16
    | exact resolve eq16 eq22604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22604
  have eq23175 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq23092
       have i₂ := eq22667
       grind)
    | exact superpose eq22667 eq23092
    | exact resolve eq23092 eq22667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22667 eq23092
  have eq23176 : False := by grind
  exact eq23176

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq67 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X0 X1) X0
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq67
    | exact resolve eq67 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq107 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq109 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  clear eq19
  have eq679 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq696 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq95 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq705 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq679 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq679
    | (have j0 := eq679 X0
       grind)
    | exact resolve eq679 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq710 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq705 X0
       have j1 := eq696 X0
       grind)
    | (have r₁ := eq705 X0
       have r₂ := eq696 X0
       grind)
    | exact resolve eq705 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq705
  have eq712 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq710 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq710
    | exact resolve eq710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0) (σ X0)
       have i₂ := eq710 X0
       grind)
    | exact superpose eq710 eq67
    | exact resolve eq67 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq712 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq712
    | exact resolve eq712 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq712
  have eq739 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq738 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq738
    | exact resolve eq738 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq746 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107 x y
       grind)
    | exact superpose eq107 eq16
    | (have j1 := eq107 x y
       grind)
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq780 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq746
       have i₂ := eq710 x
       grind)
    | exact superpose eq710 eq746
    | exact resolve eq746 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq799 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq780
       have i₂ := eq739 x
       grind)
    | exact superpose eq739 eq780
    | exact resolve eq780 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq944 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq721 X0
       have i₂ := eq739 X0
       grind)
    | exact superpose eq739 eq721
    | exact resolve eq721 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq1036 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq67 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq944 X0
       grind)
    | exact superpose eq944 eq67
    | exact resolve eq67 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq944
  have eq13939 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq14196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13939 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13939
    | (have j0 := eq13939 X0 X1
       grind)
    | exact resolve eq13939 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13939
  have eq24442 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq799
       have i₂ := eq14196 y x
       grind)
    | exact superpose eq14196 eq799
    | (have j1 := eq14196 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq799
       have r₂ := eq14196 y x
       grind)
    | (have r₁ := eq799
       have r₂ := eq14196 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq799
       have r₂ := eq14196 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq799 eq14196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq14196
  have eq24443 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq24442
  have eq24445 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24443
       grind)
    | exact superpose eq24443 eq16
    | exact resolve eq16 eq24443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24443
  have eq24446 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24445
       have i₂ := eq710 x
       grind)
    | exact superpose eq710 eq24445
    | exact resolve eq24445 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24445
  have eq24447 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24446
       have i₂ := eq739 x
       grind)
    | exact superpose eq739 eq24446
    | exact resolve eq24446 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24446
  have eq24448 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq24447
  have eq24450 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24448
       grind)
    | exact superpose eq24448 eq10
    | exact resolve eq10 eq24448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24448
  have eq24579 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24450
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24450
    | exact resolve eq24450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24450
  have eq24605 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24579
       grind)
    | exact superpose eq24579 eq16
    | exact resolve eq16 eq24579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24579
  have eq24606 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24605
       have i₂ := eq710 x
       grind)
    | exact superpose eq710 eq24605
    | exact resolve eq24605 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq24605
  have eq24607 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24606
       have i₂ := eq739 x
       grind)
    | exact superpose eq739 eq24606
    | exact resolve eq24606 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq24606
  have eq24608 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq24607
  have eq24640 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq24608
       grind)
    | exact superpose eq24608 eq10
    | exact resolve eq10 eq24608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24608
  have eq24769 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24640
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq24640
    | exact resolve eq24640 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24640
  have eq24770 : y = (M.op x x) := by grind
  clear eq24769
  have eq24800 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1036 x
       have i₂ := eq24770
       grind)
    | exact superpose eq24770 eq1036
    | exact resolve eq1036 eq24770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq24863 : y = (M.op x y) := by
    first
    | (have i₁ := eq69 x x
       have i₂ := eq24770
       grind)
    | exact superpose eq24770 eq69
    | exact resolve eq69 eq24770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq24770
  have eq25286 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24800
       grind)
    | exact superpose eq24800 eq16
    | exact resolve eq16 eq24800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24800
  have eq25369 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq25286
       have i₂ := eq24863
       grind)
    | exact superpose eq24863 eq25286
    | exact resolve eq25286 eq24863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24863 eq25286
  have eq25370 : False := by grind
  exact eq25370

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq80 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq78
  have eq99 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq100 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq99
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq122 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq122
  have eq157 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq192 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq779 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ x) X0 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq4751 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq157 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq157
    | (have j0 := eq157 x
       grind)
    | exact resolve eq157 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq4779 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4751
  have eq4784 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4779
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq4779
    | exact resolve eq4779 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779
  have eq4800 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4784
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq4784 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq4809 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4800 eq50
    | exact resolve eq50 eq4800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq5040 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq192 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq192
    | (have j0 := eq192 y
       grind)
    | exact resolve eq192 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq5066 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5040
  have eq5068 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5066
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq5066
    | exact resolve eq5066 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5066
  have eq5091 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5068
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq5068 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5068
  have eq5109 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5091 eq128
    | exact resolve eq128 eq5091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq12670 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4800 eq80
    | exact resolve eq80 eq4800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq13484 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5091 eq129
    | exact resolve eq129 eq5091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq17597 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq12670
       grind)
    | exact superpose eq12670 eq16
    | exact resolve eq16 eq12670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12670
  have eq17649 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4809 eq17597
    | exact resolve eq17597 eq4809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17597
  have eq17652 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq17649
       have r₂ := eq13 x x
       grind)
    | exact resolve eq17649 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17649
  have eq17653 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq17652
       grind)
    | exact superpose eq17652 eq44
    | exact resolve eq44 eq17652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq17686 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq4800 eq17653
    | exact resolve eq17653 eq4800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4800 eq17653
  have eq18374 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq13484
       grind)
    | exact superpose eq13484 eq16
    | exact resolve eq16 eq13484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13484
  have eq18430 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5109 eq18374
    | exact resolve eq18374 eq5109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18374
  have eq18433 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq18430
       have r₂ := eq13 x y
       grind)
    | exact resolve eq18430 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18430
  have eq18434 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18433
       grind)
    | exact superpose eq18433 eq100
    | exact resolve eq100 eq18433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq18467 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq5091 eq18434
    | exact resolve eq18434 eq5091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5091 eq18434
  have eq25239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq25240 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq25239
    | exact resolve eq25239 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25239
  have eq25251 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq25240
       have r₂ := eq28
       grind)
    | exact resolve eq25240 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25240
  have eq25257 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq25251 eq5109
    | exact resolve eq5109 eq25251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5109 eq25251
  have eq25313 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25257
       have i₂ := eq18433
       grind)
    | exact superpose eq18433 eq25257
    | exact resolve eq25257 eq18433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18433 eq25257
  have eq25322 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq25313
    | exact resolve eq25313 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25313
  have eq25323 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq25322
  have eq25331 : (τ (σ x)) = (k x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq25323 eq4809
    | exact resolve eq4809 eq25323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4809 eq25323
  have eq25409 : (τ (σ x)) = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25331
       have i₂ := eq17652
       grind)
    | exact superpose eq17652 eq25331
    | exact resolve eq25331 eq17652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17652 eq25331
  have eq25420 : x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq25409
    | exact resolve eq25409 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25409
  have eq25421 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq25420
  have eq25433 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18467
       have i₂ := eq25421
       grind)
    | exact superpose eq25421 eq18467
    | exact resolve eq18467 eq25421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18467
  have eq25443 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq55 y y
       have i₂ := eq25421
       grind)
    | exact superpose eq25421 eq55
    | exact resolve eq55 eq25421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25421
  have eq25477 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25443
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25443
    | exact resolve eq25443 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25443
  have eq25480 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25433
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25433
    | exact resolve eq25433 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25433
  have eq25528 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq779 x
       have i₂ := eq25477
       grind)
    | exact superpose eq25477 eq779
    | exact resolve eq779 eq25477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq25477
  have eq25590 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56 eq25528
    | exact resolve eq25528 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq25528
  have eq25601 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25590
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25590
    | exact resolve eq25590 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25590
  have eq25602 : y = (M.op x y) := by grind
  clear eq25601
  have eq25607 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq25602 eq21
    | exact resolve eq21 eq25602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25602
  have eq25786 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25607
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25607
    | exact resolve eq25607 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq25607
  have eq26314 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq25786 eq27
    | exact resolve eq27 eq25786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq26370 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq25786 eq783
    | exact resolve eq783 eq25786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq29211 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq25786 eq25480
    | exact resolve eq25480 eq25786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25480 eq25786
  have eq29228 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29211 eq55
    | exact resolve eq55 eq29211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq29211
  have eq29271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26314 eq29228
    | exact resolve eq29228 eq26314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29228
  have eq29281 : x = (M.op x x) := by
    first
    | (have r₁ := eq29271
       have r₂ := eq28
       grind)
    | exact resolve eq29271 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29271
  have eq29311 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17686
       have i₂ := eq29281
       grind)
    | exact superpose eq29281 eq17686
    | exact resolve eq17686 eq29281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17686 eq29281
  have eq29385 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq29311
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29311
    | exact resolve eq29311 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29311
  have eq29721 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq29385 eq26370
    | exact resolve eq26370 eq29385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26370 eq29385
  have eq29778 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq57 eq29721
    | exact resolve eq29721 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq29721
  have eq29795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26314 eq29778
    | exact resolve eq29778 eq26314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26314 eq29778
  have eq29810 : False := by grind
  exact eq29810

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
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
  have eq62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq111 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq247 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq265 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq247 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq270 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq265 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq265 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq265 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq286 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X1
       have j1 := eq111 X0 (σ X1)
       grind)
    | (have r₁ := eq270 X0 X1
       have r₂ := eq111 X0 X1
       grind)
    | exact resolve eq270 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq270
  have eq296 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq297 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq296 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq301 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq297 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq297
    | exact resolve eq297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq297 x y
       grind)
    | exact superpose eq297 eq16
    | exact resolve eq16 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq713 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq301 X0 (τ X1)
       grind)
    | exact superpose eq301 eq17
    | exact resolve eq17 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq301
  have eq737 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq713
    | exact resolve eq713 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq751 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq737 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq737
    | exact resolve eq737 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq791 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq313
       have i₂ := eq751 x y
       grind)
    | exact superpose eq751 eq313
    | exact resolve eq313 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq751
  have eq792 : False := by grind
  exact eq792

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq57 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq28
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq37 X1 X2 X0
       grind)
    | exact superpose eq37 eq33
    | exact resolve eq33 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X0 ∨ (k (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2)) X0) = X0 ∨ (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2)) ≠ X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2)) X0
       have i₂ := eq31 X1 X2 X3 X0
       grind)
    | exact superpose eq31 eq13
    | (have j0 := eq13 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2)) X0
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op (M.op (σ (k X0 X1)) X2) (σ X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq9
    | (have j1 := eq68 X1 X1
       grind)
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq33
    | (have j1 := eq68 X1 X0
       grind)
    | exact resolve eq33 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq244 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq246 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq244 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq244 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq244 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq253 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq246 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq246
    | (have j0 := eq246 (τ X0) X1
       grind)
    | exact resolve eq246 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq253 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq253
    | (have j0 := eq253 X0 X1
       grind)
    | exact resolve eq253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq258 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq255
    | (have j0 := eq255 X0 X1
       grind)
    | exact resolve eq255 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq264 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq258 (τ X0) X1
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq258
    | (have j0 := eq258 (τ X0) X1
       grind)
    | exact resolve eq258 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (M.op (τ X1) X0) X2
       have i₂ := eq71 X1 X0
       grind)
    | exact superpose eq71 eq28
    | (have j1 := eq71 X1 X0
       grind)
    | exact resolve eq28 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq71
  have eq981 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq972 X0 X1 X2
       have i₂ := eq57 X0 X1 X2
       grind)
    | exact superpose eq57 eq972
    | (have j0 := eq972 X0 X1 X2
       grind)
    | exact resolve eq972 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq972
  have eq1270 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq229
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq229
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq229 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq1271 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1270
  have eq1757 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq231 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq1758 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1757 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq2085 : ∀ X0 X1 X2 X3 X4 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k (M.op (M.op X2 X0) (M.op (M.op (M.op X3 X4) X2) X3)) X0) = X0 ∨ (M.op (M.op X2 X0) (M.op (M.op (M.op X3 X4) X2) X3)) ≠ X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq121 X0 X2 X3 X4
       grind)
    | exact superpose eq121 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq121 X0 X2 X3 X4
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq121 X0 X1 X2 X3
       grind)
    | exact resolve eq12 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2147 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X0) (M.op (M.op (M.op X3 X4) X2) X3)) ≠ X0 ∨ (k (M.op (M.op X2 X0) (M.op (M.op (M.op X3 X4) X2) X3)) X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq2085 X0 X1 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085
  have eq4623 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op (σ (k (τ X0) (τ X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1758 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1758
    | exact resolve eq1758 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq4711 : ∀ X0 X1 : G, (M.op (M.op (M.op (k (σ (τ X0)) X0) X1) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4623 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4623
    | (have j0 := eq4623 X0 X1
       grind)
    | exact resolve eq4623 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4623
  have eq4714 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X1) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4711 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4711
    | (have j0 := eq4711 X0 X1
       grind)
    | exact resolve eq4711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4711
  have eq4729 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (k X0 X0) (k X0 X0) X1
       have i₂ := eq4714 X0 (k X0 X0)
       grind)
    | exact superpose eq4714 eq31
    | (have j1 := eq4714 X0 X1
       grind)
    | exact resolve eq31 eq4714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq4730 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0 (k X0 X0) (k X0 X0)
       have i₂ := eq4714 X0 (k X0 X0)
       grind)
    | exact superpose eq4714 eq34
    | (have j1 := eq4714 X0 x
       grind)
    | exact resolve eq34 eq4714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4714
  have eq5081 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97 X0 X0 X0
       have i₂ := eq4729 X0 X1
       grind)
    | exact superpose eq4729 eq97
    | (have j1 := eq4729 X0 X2
       grind)
    | exact resolve eq97 eq4729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4729
  have eq5157 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5081 X0 X1 X2
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq5081
    | (have j0 := eq5081 X0 X1 X2
       grind)
    | exact resolve eq5081 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5081
  have eq5753 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5157 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5157
  have eq5754 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5753
  have eq6101 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (k X0 X0) X0 X0
       have i₂ := eq5754 X0
       grind)
    | exact superpose eq5754 eq34
    | exact resolve eq34 eq5754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5754
  have eq6197 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6101 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6101
    | exact resolve eq6101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6198 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6101 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq6101
    | exact resolve eq6101 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6205 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X0 X0)) = (M.op X1 (M.op (M.op X0 X1) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (k X0 X0) X0
       have i₂ := eq6101 X0
       grind)
    | exact superpose eq6101 eq34
    | exact resolve eq34 eq6101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6695 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6197 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6197
    | exact resolve eq6197 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6197
  have eq7186 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (k X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (τ (k X0 X0)) (τ X0) X1
       have i₂ := eq6198 X0
       grind)
    | exact superpose eq6198 eq37
    | exact resolve eq37 eq6198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6198
  have eq7406 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (k (σ X0) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0 (k (σ X0) (σ X0))
       have i₂ := eq4730 (σ X0)
       grind)
    | exact superpose eq4730 eq72
    | (have j0 := eq72 X0 (k (σ X0) (σ X0))
       have j1 := eq4730 (σ X0)
       grind)
    | exact resolve eq72 eq4730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq4730
  have eq7445 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (k (σ X0) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq7406 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7406
  have eq7452 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (k (σ X0) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7445 x
       have i₂ := eq22 (σ x) x
       grind)
    | exact superpose eq22 eq7445
    | (have j0 := eq7445 X0
       grind)
    | exact resolve eq7445 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7445
  have eq7464 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k (σ X0) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7452 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7452
    | (have j0 := eq7452 X0
       grind)
    | exact resolve eq7452 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7452
  have eq7467 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7464 X0
       have i₂ := eq6101 (σ X0)
       grind)
    | exact superpose eq6101 eq7464
    | (have j0 := eq7464 X0
       grind)
    | exact resolve eq7464 eq6101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6101 eq7464
  have eq7469 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq7467 X0
       have j1 := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq7467 X0
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq7467 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7467
  have eq7471 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7469 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq7469
    | (have j0 := eq7469 X0
       grind)
    | exact resolve eq7469 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7469
  have eq8197 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ (k X0 X0))) X1) (σ (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ (σ (k X0 X0))) (σ (σ X0)) X1
       have i₂ := eq6695 X0
       grind)
    | exact superpose eq6695 eq37
    | exact resolve eq37 eq6695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6695
  have eq10675 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1271
       grind)
    | exact superpose eq1271 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1271
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1271
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1271
       grind)
    | exact resolve eq13 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq10749 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq10675
  have eq10750 : x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq10749
  have eq14468 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq7471 (τ X0)
       grind)
    | exact superpose eq7471 eq18
    | (have j1 := eq7471 (τ X0)
       grind)
    | exact resolve eq18 eq7471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7471
  have eq14502 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14468 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq14468
    | (have j0 := eq14468 X0
       grind)
    | exact resolve eq14468 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14468
  have eq14538 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14502 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14502
    | (have j0 := eq14502 X0
       grind)
    | exact resolve eq14502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14502
  have eq14570 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14538 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq14538
    | (have j0 := eq14538 X0
       grind)
    | exact resolve eq14538 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq14538
  have eq14601 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14570 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14570
    | (have j0 := eq14570 X0
       grind)
    | exact resolve eq14570 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14570
  have eq14624 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq14601 X0
       have j1 := eq258 X0 (k X0 X0)
       grind)
    | (have r₁ := eq14601 X0
       have r₂ := eq258 X0 x
       grind)
    | exact resolve eq14601 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14601
  have eq14650 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14624 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq14624
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq14624 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14697 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14650 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14650
  have eq14733 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq14697 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq14697 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq14697 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14697
  have eq20060 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq14624 (τ X0)
       have i₂ := eq981 (τ X0) X0 X0
       grind)
    | exact superpose eq981 eq14624
    | (have j1 := eq981 (τ X0) X0 x
       grind)
    | exact resolve eq14624 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981 eq14624
  have eq20084 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20060 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20060
  have eq20104 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq20084 X0
       have i₂ := eq14733 (τ X0)
       grind)
    | exact superpose eq14733 eq20084
    | (have j0 := eq20084 X0
       grind)
    | exact resolve eq20084 eq14733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20084
  have eq20125 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20104 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq20104
    | (have j0 := eq20104 X0
       grind)
    | exact resolve eq20104 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20104
  have eq38817 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X0) ≠ X2 ∨ (k (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 ∨ (k X3 X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2147 X0 X1 (M.op X2 X1) X2 X2
       have i₂ := eq37 X2 X1 X2
       grind)
    | exact superpose eq37 eq2147
    | (have j0 := eq2147 X2 X3 X2 X3 x
       grind)
    | exact resolve eq2147 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2147
  have eq83156 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14733 (τ X0)
       have i₂ := eq20125 X0
       grind)
    | exact superpose eq20125 eq14733
    | (have j1 := eq20125 X0
       grind)
    | exact resolve eq14733 eq20125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14733
  have eq83303 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq20125 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20125
  have eq83363 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83156 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq83156
    | (have j0 := eq83156 X0
       grind)
    | exact resolve eq83156 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq83156
  have eq83394 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq83363 X0
       have j1 := eq83303 X0
       grind)
    | (have r₁ := eq83363 X0
       have r₂ := eq83303 X0
       grind)
    | exact resolve eq83363 eq83303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83303 eq83363
  have eq83402 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq83394 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83394
    | exact resolve eq83394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83394
  have eq83809 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq83402 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq83402
    | exact resolve eq83402 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq83402
  have eq83860 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq83809 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83809
    | exact resolve eq83809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83809
  have eq84273 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq246 X0 X1
       have i₂ := eq83860 X0
       grind)
    | exact superpose eq83860 eq246
    | (have j0 := eq246 X0 X1
       grind)
    | exact resolve eq246 eq83860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq84276 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq83860 X0
       grind)
    | exact superpose eq83860 eq264
    | (have j0 := eq264 X0 X1
       grind)
    | exact resolve eq264 eq83860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84497 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq83860 (σ X0)
       grind)
    | exact superpose eq83860 eq15
    | exact resolve eq15 eq83860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84575 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq84497 X0
       have i₂ := eq83860 X0
       grind)
    | exact superpose eq83860 eq84497
    | exact resolve eq84497 eq83860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83860 eq84497
  have eq551901 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X0 X1) X0) = X0 ∨ (k X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38817 (M.op X1 X2) (M.op X1 X2) X1 x
       have i₂ := eq9 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq9 eq38817
    | (have j0 := eq38817 X0 X1 X0 X2
       grind)
    | exact resolve eq38817 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38817
  have eq568628 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq235 y x
       have i₂ := eq10750
       grind)
    | exact superpose eq10750 eq235
    | (have j0 := eq235 x x
       grind)
    | exact resolve eq235 eq10750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq10750
  have eq568687 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq568628
  have eq568703 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq568687
       have i₂ := eq84575 x
       grind)
    | exact superpose eq84575 eq568687
    | exact resolve eq568687 eq84575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84575 eq568687
  have eq1607578 : (M.op x x) = (τ (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq568703
       grind)
    | exact superpose eq568703 eq10
    | exact resolve eq10 eq568703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568703
  have eq1608140 : x = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1607578
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1607578
    | exact resolve eq1607578 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607578
  have eq1608141 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1608140
  have eq1608590 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq551901 (σ y) (σ x) x
       have i₂ := eq1608141
       grind)
    | exact superpose eq1608141 eq551901
    | (have j0 := eq551901 (σ y) x (σ y)
       grind)
    | (have r₁ := eq551901 (σ y) (σ x) x
       have r₂ := eq1608141
       grind)
    | (have r₁ := eq551901 x x x
       have r₂ := eq1608141
       grind)
    | exact resolve eq551901 eq1608141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551901 eq1608141
  have eq1608597 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1608590 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608590
  have eq1608604 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1608597 X0
       have j1 := eq258 (σ y) X0
       grind)
    | (have r₁ := eq1608597 X0
       have r₂ := eq258 (σ y) x
       grind)
    | (have r₁ := eq1608597 (σ y)
       have r₂ := eq258 (σ y) x
       grind)
    | exact resolve eq1608597 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq1608597
  have eq1614084 : ∀ X0 X1 : G, (τ x) ≠ (τ x) ∨ (k X0 (τ x)) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84276 x X0
       have i₂ := eq1608604 X1
       grind)
    | exact superpose eq1608604 eq84276
    | (have j0 := eq84276 x X0
       have j1 := eq1608604 X1
       grind)
    | exact resolve eq84276 eq1608604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84276
  have eq1614369 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op X0 (M.op (M.op x X0) x)) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 x x
       have i₂ := eq1608604 X0
       grind)
    | exact superpose eq1608604 eq97
    | (have j1 := eq1608604 X1
       grind)
    | exact resolve eq97 eq1608604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1608604
  have eq1614705 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (k X0 (τ x)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1614084 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614084
  have eq1614813 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1614369 X1 X1
       have i₂ := eq33 x X1
       grind)
    | exact superpose eq33 eq1614369
    | (have j0 := eq1614369 X0 X1
       grind)
    | exact resolve eq1614369 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614369
  have eq1622473 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (σ y)) X0) (τ (σ y))) X0) = X0 ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq7186 (σ y) X0
       have i₂ := eq1614813 X1 (σ y)
       grind)
    | exact superpose eq1614813 eq7186
    | (have j1 := eq1614813 X1 X1
       grind)
    | exact resolve eq7186 eq1614813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7186 eq1614813
  have eq1623419 : ∀ X0 X1 : G, (M.op (τ (σ y)) X0) = X0 ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1622473 X0 X1
       have i₂ := eq33 (τ (σ y)) X0
       grind)
    | exact superpose eq33 eq1622473
    | (have j0 := eq1622473 X0 X1
       grind)
    | exact resolve eq1622473 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622473
  have eq1623787 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1623419 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1623419
    | (have j0 := eq1623419 X0 X1
       grind)
    | exact resolve eq1623419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623419
  have eq1635656 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq1623787 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623787
  have eq1635657 : x = (M.op y x) := by grind
  clear eq1635656
  have eq1635705 : y = (M.op x y) := by
    first
    | (have i₁ := eq33 y x
       have i₂ := eq1635657
       grind)
    | exact superpose eq1635657 eq33
    | exact resolve eq33 eq1635657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635657
  have eq1842463 : ∀ X0 X1 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 ∨ (k X1 (τ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264 (σ y) X0
       have i₂ := eq1614705 X1 (σ y)
       grind)
    | exact superpose eq1614705 eq264
    | (have j0 := eq264 (σ y) X0
       have j1 := eq1614705 X1 X1
       grind)
    | exact resolve eq264 eq1614705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq1614705
  have eq1843144 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ (k X1 (τ x)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1842463 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842463
  have eq1843605 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (k X1 (τ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1843144 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1843144
    | (have j0 := eq1843144 X0 X1
       grind)
    | exact resolve eq1843144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843144
  have eq1850518 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (k X1 (τ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6205 y X1
       have i₂ := eq1843605 y X1
       grind)
    | exact superpose eq1843605 eq6205
    | (have j1 := eq1843605 X0 X1
       grind)
    | exact resolve eq6205 eq1843605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843605
  have eq1851399 : ∀ X0 X1 : G, (k X1 (τ x)) = X1 ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1850518 X1 X1
       have i₂ := eq33 y X1
       grind)
    | exact superpose eq33 eq1850518
    | (have j0 := eq1850518 X0 X1
       grind)
    | exact resolve eq1850518 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850518
  have eq1859739 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ (τ x))) X0) (σ (σ (τ x)))) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq8197 (τ x) X0
       have i₂ := eq1851399 X1 (τ x)
       grind)
    | exact superpose eq1851399 eq8197
    | (have j1 := eq1851399 X1 X1
       grind)
    | exact resolve eq8197 eq1851399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8197 eq1851399
  have eq1860884 : ∀ X0 X1 : G, (M.op (σ (σ (τ x))) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1859739 X0 X1
       have i₂ := eq33 (σ (σ (τ x))) X0
       grind)
    | exact superpose eq33 eq1859739
    | (have j0 := eq1859739 X0 X1
       grind)
    | exact resolve eq1859739 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859739
  have eq1861345 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1860884 X0 X1
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq1860884
    | (have j0 := eq1860884 X0 X1
       grind)
    | exact resolve eq1860884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860884
  have eq1900688 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1861345 (σ y) X0
       grind)
    | exact superpose eq1861345 eq16
    | (have j1 := eq1861345 X0 X0
       grind)
    | exact resolve eq16 eq1861345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861345
  have eq1901538 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1900688 X0
       have i₂ := eq1635705
       grind)
    | exact superpose eq1635705 eq1900688
    | (have j0 := eq1900688 X0
       grind)
    | exact resolve eq1900688 eq1635705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635705 eq1900688
  have eq1901539 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1901538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901538
  have eq1901668 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq84273 y X0
       have i₂ := eq1901539 y
       grind)
    | exact superpose eq1901539 eq84273
    | (have j0 := eq84273 y X0
       grind)
    | exact resolve eq84273 eq1901539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84273
  have eq1902877 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1901668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901668
  have eq1927264 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq6205 (σ y) x
       have i₂ := eq1902877 (σ y)
       grind)
    | exact superpose eq1902877 eq6205
    | exact resolve eq6205 eq1902877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6205 eq1902877
  have eq1928327 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1927264 x
       have i₂ := eq33 (σ y) x
       grind)
    | exact superpose eq33 eq1927264
    | exact resolve eq1927264 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1927264
  have eq1962952 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1928327 (σ x)
       grind)
    | exact superpose eq1928327 eq16
    | exact resolve eq16 eq1928327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928327
  have eq1963170 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1962952
       have i₂ := eq1901539 x
       grind)
    | exact superpose eq1901539 eq1962952
    | exact resolve eq1962952 eq1901539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901539 eq1962952
  have eq1963171 : False := by grind
  exact eq1963171

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyy_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) x) X0) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq77 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq77
  have eq92 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63 eq12
    | (have j0 := eq12 x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq63
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq101 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq98
  have eq104 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq105 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq92 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq112 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq113 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq112
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq112 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq123
    | exact resolve eq123 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq135 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq113
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq16
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq135
  have eq168 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq203 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq326 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq567 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq326 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq326
    | (have j0 := eq326 X0 y
       grind)
    | exact resolve eq326 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq615 : (k (k x y) y) = (τ (k (k (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq72 eq567
    | exact resolve eq567 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq656 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq50 eq105
    | (have j0 := eq105 x x x
       grind)
    | exact resolve eq105 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq105
  have eq781 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X1) (σ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq54
    | (have j1 := eq73 (k X0 X1) X1
       grind)
    | exact resolve eq54 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq861 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq60
    | (have j0 := eq60 (σ x) X0 (σ y)
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq6597 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq168 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq168
    | (have j0 := eq168 x
       grind)
    | exact resolve eq168 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq6633 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6597
  have eq6641 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6633
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6633
    | exact resolve eq6633 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6633
  have eq6657 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6641
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq6641 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6641
  have eq6662 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6657 eq49
    | exact resolve eq49 eq6657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq6812 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq203 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq203
    | (have j0 := eq203 y
       grind)
    | exact resolve eq203 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq6846 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6812
  have eq6850 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6846
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq6846
    | exact resolve eq6846 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq6846
  have eq6873 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6850
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq6850 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6850
  have eq6887 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6873 eq141
    | exact resolve eq141 eq6873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9550 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq656 eq781
    | (have j0 := eq781 x x
       grind)
    | exact resolve eq781 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq781
  have eq9796 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq9550
  have eq9918 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9796
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9796
    | exact resolve eq9796 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9796
  have eq10031 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9918
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9918
    | exact resolve eq9918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9918
  have eq10137 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq10031
    | exact resolve eq10031 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10031
  have eq16861 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6657 eq79
    | exact resolve eq79 eq6657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq17416 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6873 eq142
    | exact resolve eq142 eq6873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq6873
  have eq22147 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq16861
       grind)
    | exact superpose eq16861 eq16
    | exact resolve eq16 eq16861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16861
  have eq22200 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6662 eq22147
    | exact resolve eq22147 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6662 eq22147
  have eq22203 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq22200
       have r₂ := eq13 x x
       grind)
    | exact resolve eq22200 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22200
  have eq22204 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq22203
       grind)
    | exact superpose eq22203 eq43
    | exact resolve eq43 eq22203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq22203
  have eq22236 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6657 eq22204
    | exact resolve eq22204 eq6657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6657 eq22204
  have eq23072 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq17416
       grind)
    | exact superpose eq17416 eq16
    | exact resolve eq16 eq17416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17416
  have eq23129 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6887 eq23072
    | exact resolve eq23072 eq6887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6887 eq23072
  have eq23132 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq23129
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23129 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23129
  have eq31064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq124 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq31071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq31064
    | exact resolve eq31064 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31064
  have eq31082 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq31071
       have r₂ := eq27
       grind)
    | exact resolve eq31071 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31071
  have eq31094 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31082 eq54
    | exact resolve eq54 eq31082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31082
  have eq31146 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq31094
    | exact resolve eq31094 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31094
  have eq31160 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31146 eq865
    | exact resolve eq865 eq31146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31146
  have eq31236 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56 eq31160
    | exact resolve eq31160 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31160
  have eq31248 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq31236
    | exact resolve eq31236 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31236
  have eq31249 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq31248
  have eq31272 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq31249
       grind)
    | exact superpose eq31249 eq54
    | exact resolve eq54 eq31249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31249
  have eq31324 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31272
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31272
    | exact resolve eq31272 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31272
  have eq31806 : y = (M.op (M.op (M.op x y) x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq861 x
       have i₂ := eq31324
       grind)
    | exact superpose eq31324 eq861
    | exact resolve eq861 eq31324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq31324
  have eq31881 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55 eq31806
    | exact resolve eq31806 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq31806
  have eq31894 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31881
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31881
    | exact resolve eq31881 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31881
  have eq31895 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq31894
  have eq31906 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31895 eq101
    | exact resolve eq101 eq31895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq31895
  have eq34152 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31906 eq72
    | exact resolve eq72 eq31906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31906
  have eq34180 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq34152
    | exact resolve eq34152 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34152
  have eq34309 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34180 eq13
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq34180
       grind)
    | exact resolve eq13 eq34180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34180
  have eq34354 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34309 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34309
  have eq34616 : (τ (σ y)) = (k x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34354 eq72
    | exact resolve eq72 eq34354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq34354
  have eq34692 : y = (k x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq34616
    | exact resolve eq34616 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34616
  have eq34693 : y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq34692
  have eq34748 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq34693
       grind)
    | exact superpose eq34693 eq44
    | exact resolve eq44 eq34693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq34693
  have eq34781 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34748
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34748
    | exact resolve eq34748 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34748
  have eq34930 : (τ (k (σ y) (σ y))) = (k (k x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34781 eq615
    | exact resolve eq615 eq34781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq34781
  have eq34946 : (k y y) = (k (k x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq141 eq34930
    | exact resolve eq34930 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq34930
  have eq34955 : (M.op y y) = (k (k x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34946
       have i₂ := eq23132
       grind)
    | exact superpose eq23132 eq34946
    | exact resolve eq34946 eq23132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23132 eq34946
  have eq35505 : (M.op y y) = (k (M.op y x) y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34955
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq34955
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq34955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34955
  have eq35523 : (M.op y y) = (k (M.op y x) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op y x) y
       grind)
    | (have r₁ := eq35505
       have r₂ := eq13 x y
       grind)
    | exact resolve eq35505 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35505
  have eq35530 : y = (M.op x y) ∨ (M.op y y) = (k (M.op y x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35523
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35523
    | exact resolve eq35523 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35523
  have eq35531 : (M.op y y) = (k (M.op y x) y) ∨ y = (M.op x y) := by grind
  clear eq35530
  have eq35812 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq104 y x
       have i₂ := eq35531
       grind)
    | exact superpose eq35531 eq104
    | (have j0 := eq104 y x
       grind)
    | exact resolve eq104 eq35531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq35531
  have eq35820 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq35812
  have eq35855 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq57 X0 y y
       have i₂ := eq35820
       grind)
    | exact superpose eq35820 eq57
    | exact resolve eq57 eq35820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq35820
  have eq35914 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq35855 x
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq35855
    | exact resolve eq35855 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35855
  have eq36313 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35914 x
       grind)
    | exact superpose eq35914 eq18
    | (have j1 := eq35914 x
       grind)
    | exact resolve eq18 eq35914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35914
  have eq36374 : y = (M.op x y) := by grind
  clear eq36313
  have eq36390 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36374 eq20
    | exact resolve eq20 eq36374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq36374
  have eq36587 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36390
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36390
    | exact resolve eq36390 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq36390
  have eq36627 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq36587 eq26
    | exact resolve eq26 eq36587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq36690 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq36587 eq865
    | exact resolve eq865 eq36587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10137 eq865
    | exact resolve eq865 eq10137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq10137
  have eq37298 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq36587 eq37216
    | exact resolve eq37216 eq36587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36587 eq37216
  have eq37317 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56 eq37298
    | exact resolve eq37298 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37298
  have eq37330 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq36627 eq37317
    | exact resolve eq37317 eq36627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37317
  have eq37335 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq37330
       have r₂ := eq27
       grind)
    | exact resolve eq37330 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37330
  have eq37856 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq37335 eq54
    | exact resolve eq54 eq37335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq37335
  have eq37907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq36627 eq37856
    | exact resolve eq37856 eq36627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37856
  have eq37908 : x = (M.op x x) := by
    first
    | (have r₁ := eq37907
       have r₂ := eq27
       grind)
    | exact resolve eq37907 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37907
  have eq37917 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22236
       have i₂ := eq37908
       grind)
    | exact superpose eq37908 eq22236
    | exact resolve eq22236 eq37908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22236 eq37908
  have eq38006 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq37917
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37917
    | exact resolve eq37917 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37917
  have eq40017 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq38006 eq36690
    | exact resolve eq36690 eq38006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36690 eq38006
  have eq40090 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq56 eq40017
    | exact resolve eq40017 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq40017
  have eq40108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36627 eq40090
    | exact resolve eq40090 eq36627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36627 eq40090
  have eq40124 : False := by grind
  exact eq40124
