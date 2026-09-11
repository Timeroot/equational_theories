import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_x_pxy_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
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
  clear eq43
  have eq63 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | (have i₁ := eq14 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq64 X0 (M.op x x)
       have i₂ := eq64 (M.op x x) x
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq64 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq65 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq65
    | exact resolve eq65 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq220 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op x y) y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq217 eq14
    | exact resolve eq14 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq220 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq220
    | exact resolve eq220 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq341 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq353 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq204 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) y)
       have r₂ := eq204 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq358 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq476 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq114 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq114
    | (have j0 := eq114 (σ X0)
       grind)
    | exact resolve eq114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq63 x x X2 X3 X5
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq63
    | exact resolve eq63 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq517 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X5) := by
    intro X5
    first
    | (have i₁ := eq516 x x X5
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq516
    | exact resolve eq516 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq814 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 X0 (σ X0)
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq824 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq814 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq825 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq824 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq833 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq825
    | (have j0 := eq825 X0 X1
       grind)
    | exact resolve eq825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq834 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq833 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq893 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq358 eq341
    | exact resolve eq341 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq358
  have eq922 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq893 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq893
    | exact resolve eq893 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq4358 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq476 X0
       grind)
    | exact superpose eq476 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq476 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq476 X0
       grind)
    | exact resolve eq13 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq4385 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4358 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq4358 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq4358 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4358
  have eq5067 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq834 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq834
    | (have j0 := eq834 x X0
       grind)
    | exact resolve eq834 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq12553 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4385 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq4385
    | (have j0 := eq4385 (τ X0) X1
       grind)
    | exact resolve eq4385 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq12574 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12553 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12553
    | (have j0 := eq12553 X0 X1
       grind)
    | exact resolve eq12553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12553
  have eq12586 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12574 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12574
    | (have j0 := eq12574 X0 X1
       grind)
    | exact resolve eq12574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12574
  have eq17031 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5067 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5067
    | (have j0 := eq5067 y
       grind)
    | exact resolve eq5067 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5067
  have eq17045 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17031
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq17031
    | exact resolve eq17031 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq17031
  have eq17062 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq17045
    | exact resolve eq17045 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17045
  have eq17070 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17062 eq95
    | exact resolve eq95 eq17062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq18500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq98 eq17062
    | exact resolve eq17062 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq17062
  have eq18507 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq18500
       have r₂ := eq27
       grind)
    | exact resolve eq18500 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18500
  have eq18529 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq18507 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq18507
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq18507
       grind)
    | exact resolve eq13 eq18507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18507
  have eq18543 : ∀ X0 : G, (M.op x y) = (M.op y x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq18529 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18529
  have eq19126 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18543 X0
       grind)
    | (have i₁ := eq12 X0 x
       have i₂ := eq18543 (M.op X0 x)
       grind)
    | exact superpose eq18543 eq12
    | (have j0 := eq12 X0 x
       have j1 := eq18543 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18543 X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18543 X0
       grind)
    | exact resolve eq12 eq18543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18543
  have eq19135 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq19126 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19126
  have eq19140 : ∀ X0 : G, (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq19135 X0
       grind)
    | (have r₁ := eq19135 X0
       have r₂ := eq18
       grind)
    | exact resolve eq19135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19135
  have eq19154 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq17070
       have i₂ := eq19140 X0
       grind)
    | (have i₁ := eq17070
       have i₂ := eq19140 (k y x)
       grind)
    | exact superpose eq19140 eq17070
    | (have j1 := eq19140 X0
       grind)
    | exact resolve eq17070 eq19140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17070 eq19140
  have eq19161 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq19154 X0
       have j1 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq19154 X0
       have r₂ := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq19154 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq19154 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19154
  have eq19172 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq19161 X1
       grind)
    | exact superpose eq19161 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq19161 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq19161 X0
       grind)
    | exact resolve eq13 eq19161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19161
  have eq19185 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq19172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19172
  have eq19225 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq19185 (k sF2 sF2) x
       grind)
    | exact superpose eq19185 eq49
    | (have j1 := eq19185 X0 x
       grind)
    | exact resolve eq49 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq19185
  have eq19323 : ∀ X0 : G, x = (k x x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq19225
    | (have j0 := eq19225 x
       grind)
    | exact resolve eq19225 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19225
  have eq19359 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq19323 X0
       have j1 := eq12586 x X0
       grind)
    | (have r₁ := eq19323 X0
       have r₂ := eq12586 x x
       grind)
    | (have r₁ := eq19323 x
       have r₂ := eq12586 x x
       grind)
    | exact resolve eq19323 eq12586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12586 eq19323
  have eq19418 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq4385 x X0
       have i₂ := eq19359 x
       grind)
    | exact superpose eq19359 eq4385
    | (have j0 := eq4385 x X0
       grind)
    | exact resolve eq4385 eq19359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4385 eq19359
  have eq19453 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq19418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19418
  have eq19474 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq19453 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19453
    | (have j0 := eq19453 X0
       grind)
    | exact resolve eq19453 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19453
  have eq19607 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19474 eq114
    | (have j0 := eq114 (σ x)
       grind)
    | exact resolve eq114 eq19474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19474
  have eq19640 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq19607
  have eq20332 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ x)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq19640 eq64
    | exact resolve eq64 eq19640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq22555 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20332 eq19640
    | exact resolve eq19640 eq20332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19640 eq20332
  have eq22558 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq22555
  have eq22579 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq22558 eq221
    | exact resolve eq221 eq22558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq22558
  have eq22638 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22579
    | exact resolve eq22579 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22579
  have eq22639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22638 eq15
    | exact resolve eq15 eq22638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22638
  have eq22699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22639
    | exact resolve eq22639 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22639
  have eq22700 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22699
       have r₂ := eq27
       grind)
    | exact resolve eq22699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22699
  have eq22703 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq22700 eq217
    | exact resolve eq217 eq22700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq22704 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq22700 eq27
    | exact resolve eq27 eq22700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq22705 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq26 eq22703
    | exact resolve eq22703 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq22703
  have eq22706 : (σ x) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq22700 eq22705
    | exact resolve eq22705 eq22700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22700 eq22705
  have eq22714 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq22706 eq517
    | exact resolve eq517 eq22706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq22720 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq22706 eq922
    | exact resolve eq922 eq22706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq22765 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq22720
    | exact resolve eq22720 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq22720
  have eq23672 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114 x
       have i₂ := eq22765 x
       grind)
    | exact superpose eq22765 eq114
    | (have j0 := eq114 x
       grind)
    | exact resolve eq114 eq22765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq22765
  have eq23707 : x = (M.op x x) := by grind
  clear eq23672
  have eq24690 : (M.op (M.op x y) y) = (M.op x x) := by
    first
    | (have i₁ := eq206 x x
       have i₂ := eq23707
       grind)
    | exact superpose eq23707 eq206
    | exact resolve eq206 eq23707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq24693 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq24690
       have i₂ := eq23707
       grind)
    | exact superpose eq23707 eq24690
    | exact resolve eq24690 eq23707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23707 eq24690
  have eq24704 : x = (σ x) := by
    first
    | exact superpose eq22706 eq24693
    | exact resolve eq24693 eq22706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22706 eq24693
  have eq24812 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq24704 eq22714
    | exact resolve eq22714 eq24704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22714 eq24704
  have eq30156 : x = (M.op x y) := by
    first
    | (have i₁ := eq24812 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24812
    | (have j0 := eq24812 y
       grind)
    | exact resolve eq24812 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24812
  have eq30230 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30156 eq20
    | exact resolve eq20 eq30156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30156
  have eq30432 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30230
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30230
    | exact resolve eq30230 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq30230
  have eq30528 : False := by grind
  exact eq30528

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pxx_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq174 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op x x) X4 X5
       have i₂ := eq16 (M.op x x) x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 (M.op x (M.op X1 X1)) X1 x x
       have i₂ := eq16 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | (have i₁ := eq16 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq178 x x X2 X3 X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq185 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq184 x x X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq184
    | exact resolve eq184 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq186 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 (M.op x x)
       have i₂ := eq179 (M.op x x) x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq179 x x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op x x) X2 X3
       have i₂ := eq179 (M.op x x) x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq180
  have eq219 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq202 eq185
    | exact resolve eq185 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq185 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq185 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq227 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq234 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq202 eq231
    | exact resolve eq231 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq231
  have eq318 : (τ (σ y)) = (k y (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq234 eq107
    | exact resolve eq107 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq329 : y = (k y (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq31 eq318
    | exact resolve eq318 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq456 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq234 eq34
    | exact resolve eq34 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq234
  have eq484 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq456 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq456
    | exact resolve eq456 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq582 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq603 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq651 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq219 eq12
    | (have j0 := eq12 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op x y) y) X0
       have r₂ := eq219 X0
       grind)
    | exact resolve eq12 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq660 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq186 eq657
    | (have j0 := eq657 X0
       grind)
    | exact resolve eq657 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq667 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq660 X0
       have j1 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq660 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq660 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq682 : (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) x) := by
    first
    | exact superpose eq667 eq141
    | exact resolve eq141 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq667
  have eq751 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq484 eq604
    | (have j0 := eq604 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq604 (σ (M.op (M.op x y) y))
       have r₂ := eq484 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq604 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq757 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq751
  have eq1872 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq582
       grind)
    | exact superpose eq582 eq39
    | exact resolve eq39 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1873 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1872
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1872
    | exact resolve eq1872 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872
  have eq1875 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1873
    | exact resolve eq1873 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq14070 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq757 eq191
    | exact resolve eq191 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq14073 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (σ (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq757 eq14070
    | exact resolve eq14070 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq14070
  have eq14084 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq186 eq14073
    | exact resolve eq14073 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq14073
  have eq14129 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq14084 eq15
    | exact resolve eq15 eq14084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1875 eq598
    | exact resolve eq598 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq20818 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq20810
       have r₂ := eq27
       grind)
    | exact resolve eq20810 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20810
  have eq21104 : (M.op (M.op x y) y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20818 eq190
    | exact resolve eq190 eq20818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21109 : (σ y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20818 eq21104
    | exact resolve eq21104 eq20818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20818 eq21104
  have eq21154 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21109 eq682
    | exact resolve eq682 eq21109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq21109
  have eq21272 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq13 (τ (σ y)) x
       grind)
    | (have r₁ := eq21154
       have r₂ := eq13 x (σ x)
       grind)
    | (have r₁ := eq21154
       have r₂ := eq13 x x
       grind)
    | exact resolve eq21154 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21154
  have eq21336 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq21272
    | exact resolve eq21272 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq21272
  have eq21505 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21336 eq190
    | exact resolve eq190 eq21336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21510 : (σ x) = (M.op (M.op x y) y) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21336 eq21505
    | exact resolve eq21505 eq21336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21336 eq21505
  have eq21550 : y = (k y (τ (σ x))) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21510 eq329
    | exact resolve eq329 eq21510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq21510
  have eq21700 : y = (k y x) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq21550
    | exact resolve eq21550 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21550
  have eq21701 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq21700
  have eq21767 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq582
       have i₂ := eq21701
       grind)
    | exact superpose eq21701 eq582
    | exact resolve eq582 eq21701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq21769 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq21701
       grind)
    | exact superpose eq21701 eq39
    | exact resolve eq39 eq21701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21772 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq21767
  have eq21774 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq21769
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21769
    | exact resolve eq21769 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21769
  have eq21784 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21774 eq598
    | exact resolve eq598 eq21774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21774
  have eq21816 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 y x X2 X0 X1
       have i₂ := eq21772
       grind)
    | exact superpose eq21772 eq174
    | exact resolve eq174 eq21772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21820 : (M.op (M.op x y) y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq190 y x
       have i₂ := eq21772
       grind)
    | exact superpose eq21772 eq190
    | exact resolve eq190 eq21772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21825 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21772 eq21820
    | exact resolve eq21820 eq21772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21820
  have eq21829 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X2
    first
    | (have i₁ := eq21816 x x X2
       have i₂ := eq190 x x
       grind)
    | (have i₁ := eq21816 x y X2
       have i₂ := eq190 X2 x
       grind)
    | exact superpose eq190 eq21816
    | (have j0 := eq21816 x y X2
       grind)
    | exact resolve eq21816 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21816
  have eq21836 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X2
    first
    | exact superpose eq21772 eq21829
    | exact resolve eq21829 eq21772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21772 eq21829
  have eq21838 : ∀ X2 : G, y = (M.op X2 y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X2
    first
    | exact superpose eq21825 eq21836
    | exact resolve eq21836 eq21825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21836
  have eq21951 : y = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21825 eq14084
    | exact resolve eq14084 eq21825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21825
  have eq21973 : x = (M.op x x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq21951
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21951
    | exact resolve eq21951 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21951
  have eq22380 : (M.op (M.op x y) y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq190 x x
       have i₂ := eq21973
       grind)
    | exact superpose eq21973 eq190
    | exact resolve eq190 eq21973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22385 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq21973 eq22380
    | exact resolve eq22380 eq21973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21973 eq22380
  have eq22621 : x = (σ x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq22385 eq14084
    | exact resolve eq14084 eq22385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22631 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) ∨ y = (M.op x y) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq22385 eq175
    | exact resolve eq175 eq22385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22633 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq22385 eq190
    | exact resolve eq190 eq22385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22385
  have eq22638 : y = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22633
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22633
    | exact resolve eq22633 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22633
  have eq22640 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq22631 x x
       have i₂ := eq190 x x
       grind)
    | (have i₁ := eq22631 x y
       have i₂ := eq190 x x
       grind)
    | exact superpose eq190 eq22631
    | (have j0 := eq22631 x y
       grind)
    | exact resolve eq22631 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22631
  have eq22644 : x = (σ x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq22621
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22621
    | exact resolve eq22621 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22621
  have eq22708 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq22640
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22640
    | exact resolve eq22640 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22640
  have eq22712 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq22638 eq22644
    | exact resolve eq22644 eq22638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22644
  have eq23093 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq22712 eq26
    | exact resolve eq26 eq22712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23094 : x = (τ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq22712 eq29
    | exact resolve eq29 eq22712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22712
  have eq23205 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq22638 eq23094
    | exact resolve eq23094 eq22638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22638 eq23094
  have eq23641 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq23205 eq14
    | exact resolve eq14 eq23205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23205
  have eq23712 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq23641
    | exact resolve eq23641 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23641
  have eq24707 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq22708 eq219
    | exact resolve eq219 eq22708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22708
  have eq25871 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq24707 eq23093
    | exact resolve eq23093 eq24707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23093 eq24707
  have eq25903 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq25871
  have eq26151 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq25903 eq27
    | exact resolve eq27 eq25903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25903
  have eq26163 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26151
       have r₂ := eq23712
       grind)
    | exact resolve eq26151 eq23712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23712 eq26151
  have eq26169 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26163
       grind)
    | exact superpose eq26163 eq18
    | exact resolve eq18 eq26163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26177 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq219 X0
       have i₂ := eq26163
       grind)
    | exact superpose eq26163 eq219
    | exact resolve eq219 eq26163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26269 : (M.op (M.op x y) (σ y)) = (σ (M.op (M.op x y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14084
       have i₂ := eq26163
       grind)
    | exact superpose eq26163 eq14084
    | exact resolve eq14084 eq26163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29577 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21838 x
       grind)
    | exact superpose eq21838 eq18
    | (have j1 := eq21838 x
       grind)
    | exact resolve eq18 eq21838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21838
  have eq29671 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq29577
  have eq29754 : (M.op (M.op x y) y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq190 x x
       have i₂ := eq29671
       grind)
    | exact superpose eq29671 eq190
    | exact resolve eq190 eq29671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29763 : (M.op x x) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26163 eq29754
    | exact resolve eq29754 eq26163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29754
  have eq29777 : x = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29671 eq29763
    | exact resolve eq29763 eq29671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29671 eq29763
  have eq29945 : x = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29777 eq26269
    | exact resolve eq26269 eq29777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29951 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op x (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq29777 eq174
    | exact resolve eq174 eq29777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29955 : (M.op (M.op x y) y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29777 eq190
    | exact resolve eq190 eq29777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29960 : x = (σ x) ∨ y = (M.op x y) := by grind
  clear eq29945
  have eq29969 : (M.op (M.op x y) (σ y)) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26163 eq29955
    | exact resolve eq29955 eq26163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29955
  have eq29973 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op x (σ y))) ∨ y = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq29951 x x X2
       have i₂ := eq190 x x
       grind)
    | (have i₁ := eq29951 x y X2
       have i₂ := eq190 X2 x
       grind)
    | exact superpose eq190 eq29951
    | (have j0 := eq29951 x y X2
       grind)
    | exact resolve eq29951 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29951
  have eq29975 : y = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq29960
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29960
    | exact resolve eq29960 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29960
  have eq29977 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26169 eq29969
    | exact resolve eq29969 eq26169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29969
  have eq29980 : ∀ X2 : G, (M.op (M.op x y) (σ y)) = (M.op X2 (M.op x (σ y))) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq26163 eq29973
    | exact resolve eq29973 eq26163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26163 eq29973
  have eq29985 : ∀ X2 : G, (M.op (M.op x y) (σ y)) = (M.op X2 (M.op x y)) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq26169 eq29980
    | exact resolve eq29980 eq26169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26169 eq29980
  have eq29987 : ∀ X2 : G, x = (M.op X2 (M.op x y)) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq29777 eq29985
    | exact resolve eq29985 eq29777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29985
  have eq29989 : ∀ X2 : G, (σ x) = (M.op X2 (M.op x y)) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq29975 eq29987
    | exact resolve eq29987 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29987
  have eq29993 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq24
       have i₂ := eq29975
       grind)
    | exact superpose eq29975 eq24
    | exact resolve eq24 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30189 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq29993
    | exact resolve eq29993 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29993
  have eq30870 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29977 eq26269
    | exact resolve eq26269 eq29977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26269
  have eq30886 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq30870
  have eq30901 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq30886
    | exact resolve eq30886 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30886
  have eq31735 : (σ x) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29989 eq26177
    | exact resolve eq26177 eq29989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26177 eq29989
  have eq31742 : (σ x) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq31735
  have eq31748 : (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29977 eq31742
    | exact resolve eq31742 eq29977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29977 eq31742
  have eq31857 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31748 eq26
    | exact resolve eq26 eq31748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31995 : x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29777 eq31857
    | exact resolve eq31857 eq29777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29777 eq31857
  have eq32045 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29975 eq31995
    | exact resolve eq31995 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29975 eq31995
  have eq32089 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31748 eq32045
    | exact resolve eq32045 eq31748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31748 eq32045
  have eq32176 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32089 eq27
    | exact resolve eq27 eq32089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32089
  have eq32185 : y = (M.op x y) := by
    first
    | (have r₁ := eq32176
       have r₂ := eq30901
       grind)
    | exact resolve eq32176 eq30901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30901 eq32176
  have eq32189 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq32185
       grind)
    | exact superpose eq32185 eq18
    | exact resolve eq18 eq32185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq32190 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq32185
       grind)
    | exact superpose eq32185 eq24
    | exact resolve eq24 eq32185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq32197 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq219 X0
       have i₂ := eq32185
       grind)
    | exact superpose eq32185 eq219
    | exact resolve eq219 eq32185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq32289 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14084
       have i₂ := eq32185
       grind)
    | exact superpose eq32185 eq14084
    | exact resolve eq14084 eq32185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14084
  have eq32290 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14129
       have i₂ := eq32185
       grind)
    | exact superpose eq32185 eq14129
    | exact resolve eq14129 eq32185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14129
  have eq32295 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq21701
       have i₂ := eq32185
       grind)
    | exact superpose eq32185 eq21701
    | exact resolve eq21701 eq32185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21701
  have eq32519 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32190 eq20
    | exact resolve eq20 eq32190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32955 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq32189 eq175
    | exact resolve eq175 eq32189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq39729 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq32295 eq39
    | exact resolve eq39 eq32295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq32295
  have eq39736 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq39729
    | exact resolve eq39729 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39729
  have eq39743 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq32519 eq39736
    | exact resolve eq39736 eq32519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39736
  have eq39776 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq39743 eq598
    | exact resolve eq598 eq39743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq39743
  have eq92269 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq21784 eq174
    | exact resolve eq174 eq21784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92276 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21784 eq32955
    | exact resolve eq32955 eq21784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21784
  have eq92285 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op (σ y) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq92276
       have i₂ := eq32185
       grind)
    | exact superpose eq32185 eq92276
    | exact resolve eq92276 eq32185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92276
  have eq92292 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X2
    first
    | (have i₁ := eq92269 x x X2
       have i₂ := eq190 x x
       grind)
    | (have i₁ := eq92269 x y X2
       have i₂ := eq190 X2 x
       grind)
    | exact superpose eq190 eq92269
    | (have j0 := eq92269 x y X2
       grind)
    | exact resolve eq92269 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92269
  have eq92297 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq39776 eq92285
    | exact resolve eq92285 eq39776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92285
  have eq92304 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X2
    first
    | (have i₁ := eq92292 X2
       have i₂ := eq32185
       grind)
    | exact superpose eq32185 eq92292
    | exact resolve eq92292 eq32185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92292
  have eq92313 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X2
    first
    | (have i₁ := eq92304 X2
       have i₂ := eq32185
       grind)
    | exact superpose eq32185 eq92304
    | (have j0 := eq92304 X2
       grind)
    | exact resolve eq92304 eq32185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92304
  have eq92318 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (M.op (M.op x y) (M.op x y)) = (M.op X2 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X2
    first
    | exact superpose eq39776 eq92313
    | exact resolve eq92313 eq39776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39776 eq92313
  have eq92320 : ∀ X2 : G, (σ y) = (M.op X2 (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X2
    first
    | exact superpose eq92297 eq92318
    | exact resolve eq92318 eq92297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92297 eq92318
  have eq92729 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq92320 eq26
    | (have j1 := eq92320 (σ x)
       grind)
    | exact resolve eq26 eq92320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92320
  have eq92736 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq92729
  have eq92751 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq92736 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq92736
       grind)
    | exact resolve eq13 eq92736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92736
  have eq92778 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq92751 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92751
  have eq92819 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op x y) x)) ∨ (k X3 (σ x)) = X3 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq174 X0 X1 X2 x x
       have i₂ := eq92778 (M.op X0 X1)
       grind)
    | exact superpose eq92778 eq174
    | (have j1 := eq92778 X3
       grind)
    | exact resolve eq174 eq92778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq92826 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32955 X0 x
       have i₂ := eq92778 (M.op X0 x)
       grind)
    | exact superpose eq92778 eq32955
    | (have j1 := eq92778 X0
       grind)
    | exact resolve eq32955 eq92778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92828 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq92778 eq92826
    | (have j0 := eq92826 X0
       have j1 := eq92778 X0
       grind)
    | exact resolve eq92826 eq92778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92826
  have eq92835 : ∀ X2 X3 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (M.op x y) x)) ∨ (k X3 (σ x)) = X3 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2 X3
    first
    | (have i₁ := eq92819 x x X2 X3
       have i₂ := eq190 x x
       grind)
    | (have i₁ := eq92819 x y X2 X3
       have i₂ := eq190 X2 X3
       grind)
    | exact superpose eq190 eq92819
    | (have j0 := eq92819 x y X2 X3
       grind)
    | exact resolve eq92819 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq92819
  have eq92844 : ∀ X2 X3 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) x)) ∨ (k X3 (σ x)) = X3 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2 X3
    first
    | (have i₁ := eq92835 X2 X3
       have i₂ := eq32185
       grind)
    | exact superpose eq32185 eq92835
    | (have j0 := eq92835 X2 X3
       grind)
    | exact resolve eq92835 eq32185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32185 eq92835
  have eq92849 : ∀ X2 X3 : G, (M.op x y) = (M.op X2 (M.op (M.op x y) x)) ∨ (k X3 (σ x)) = X3 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2 X3
    first
    | exact superpose eq92828 eq92844
    | (have j0 := eq92844 X2 X3
       have j1 := eq92828 X3
       grind)
    | exact resolve eq92844 eq92828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92828 eq92844
  have eq92851 : ∀ X2 X3 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ (k X3 (σ x)) = X3 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2 X3
    first
    | exact superpose eq92778 eq92849
    | (have j0 := eq92849 X2 X3
       have j1 := eq92778 X3
       grind)
    | exact resolve eq92849 eq92778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92778 eq92849
  have eq92941 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32289
       have i₂ := eq92851 x (M.op sF0 sF0)
       grind)
    | exact superpose eq92851 eq32289
    | (have j1 := eq92851 x X0
       grind)
    | exact resolve eq32289 eq92851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32289
  have eq92955 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq92941
    | (have j0 := eq92941 X0
       grind)
    | exact resolve eq92941 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92941
  have eq92983 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32519 eq92955
    | (have j0 := eq92955 X0
       grind)
    | exact resolve eq92955 eq32519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92955
  have eq93010 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq92983 eq604
    | (have j0 := eq604 (σ x)
       grind)
    | (have r₁ := eq604 (σ x)
       have r₂ := eq92983 (σ x)
       grind)
    | exact resolve eq604 eq92983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92983
  have eq93161 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq93010
  have eq93473 : (M.op (σ x) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93161 eq32955
    | exact resolve eq32955 eq93161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93478 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93161 eq93473
    | exact resolve eq93473 eq93161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93161 eq93473
  have eq93996 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq93478 eq32197
    | exact resolve eq32197 eq93478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32197
  have eq94000 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93478 eq32290
    | exact resolve eq32290 eq93478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93478
  have eq94057 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq94000
    | exact resolve eq94000 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94000
  have eq94082 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq94057 eq27
    | exact resolve eq27 eq94057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94057
  have eq94107 : (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq94082
       have r₂ := eq30189
       grind)
    | exact resolve eq94082 eq30189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30189 eq94082
  have eq94109 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq94107 eq26
    | exact resolve eq26 eq94107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94569 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq94109 eq92851
    | (have j0 := eq92851 x X0
       grind)
    | exact resolve eq92851 eq94109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92851 eq94109
  have eq94591 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq94107 eq94569
    | (have j0 := eq94569 X0
       grind)
    | exact resolve eq94569 eq94107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94569
  have eq94592 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq94591 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94591
  have eq95237 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93996 eq26
    | (have j1 := eq93996 (σ y)
       grind)
    | exact resolve eq26 eq93996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93996
  have eq95374 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95237 eq27
    | exact resolve eq27 eq95237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95237
  have eq95402 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq95374
       have r₂ := eq32519
       grind)
    | exact resolve eq95374 eq32519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95374
  have eq95409 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq95402 eq185
    | exact resolve eq185 eq95402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq95433 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq95409
    | (have j0 := eq95409 X0
       grind)
    | exact resolve eq95409 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95409
  have eq95442 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq95402 eq95433
    | exact resolve eq95433 eq95402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95402 eq95433
  have eq99439 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq94592 eq604
    | (have j0 := eq604 (σ x)
       grind)
    | (have r₁ := eq604 (σ x)
       have r₂ := eq94592 (σ x)
       grind)
    | exact resolve eq604 eq94592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq94592
  have eq99596 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq99439
  have eq100123 : (M.op (σ x) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq99596 eq32955
    | exact resolve eq32955 eq99596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32955
  have eq100129 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq99596 eq100123
    | exact resolve eq100123 eq99596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99596 eq100123
  have eq100769 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq100129 eq32290
    | exact resolve eq32290 eq100129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32290 eq100129
  have eq100833 : x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq100769
    | exact resolve eq100769 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq100769
  have eq100834 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq100833
  have eq100855 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq100834 eq27
    | exact resolve eq27 eq100834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100834
  have eq100880 : (M.op x y) ≠ (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq32519 eq100855
    | exact resolve eq100855 eq32519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100855
  have eq100885 : x = (σ x) := by
    first
    | (have r₁ := eq100880
       have r₂ := eq94107
       grind)
    | exact resolve eq100880 eq94107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94107 eq100880
  have eq100887 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq100885
       grind)
    | exact superpose eq100885 eq22
    | exact resolve eq22 eq100885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq100968 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq32189
       have i₂ := eq100885
       grind)
    | exact superpose eq100885 eq32189
    | exact resolve eq32189 eq100885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32189 eq100885
  have eq101541 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq100968 eq95442
    | exact resolve eq95442 eq100968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95442
  have eq101560 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq101541 eq26
    | exact resolve eq26 eq101541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101864 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq100968 eq101560
    | exact resolve eq101560 eq100968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101560
  have eq101950 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq101864 eq27
    | exact resolve eq27 eq101864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101864
  have eq101976 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq32519 eq101950
    | exact resolve eq101950 eq32519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32519 eq101950
  have eq101980 : (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq101976
       have r₂ := eq101541
       grind)
    | exact resolve eq101976 eq101541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101541 eq101976
  have eq102145 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq101980 eq100887
    | exact resolve eq100887 eq101980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100887 eq101980
  have eq102576 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq102145 eq32190
    | exact resolve eq32190 eq102145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32190
  have eq102577 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq102145 eq20
    | exact resolve eq20 eq102145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq102145
  have eq103111 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq102576 eq26
    | exact resolve eq26 eq102576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq102576
  have eq103414 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq100968 eq103111
    | exact resolve eq103111 eq100968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100968 eq103111
  have eq105660 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq103414 eq27
    | exact resolve eq27 eq103414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq103414
  have eq105683 : False := by grind
  exact eq105683

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation4504 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq93 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq106
    | exact resolve eq106 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq123
  have eq127 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq126
  have eq219 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq58 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq58 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq59 x x
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq382 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq219 (M.op x X1) X1
       have i₂ := eq219 x X1
       grind)
    | (have i₁ := eq219 (M.op x y) y
       have i₂ := eq219 x X1
       grind)
    | exact superpose eq219 eq219
    | exact resolve eq219 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq396 : (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq127 eq45
    | exact resolve eq45 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq127
  have eq418 : (M.op (M.op x y) y) = (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq396
       have i₂ := eq58 (M.op sF1 sF1) sF1
       grind)
    | exact superpose eq58 eq396
    | exact resolve eq396 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq421 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq418
       have i₂ := eq58 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq58 eq418
    | exact resolve eq418 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq418
  have eq426 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq421 eq16
    | exact resolve eq16 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq935
    | exact resolve eq935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq939 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq936
       have r₂ := eq28
       grind)
    | exact resolve eq936 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq941 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq939
    | exact resolve eq939 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq944 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq941 eq227
    | exact resolve eq227 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq948 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq944
    | exact resolve eq944 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq2322 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq948 eq382
    | exact resolve eq382 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2324 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq948 eq426
    | exact resolve eq426 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq948
  have eq2478 : (σ x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq941 eq2324
    | exact resolve eq2324 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2324
  have eq2507 : (σ x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2478
  have eq2510 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2507
    | exact resolve eq2507 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq2515 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2510 eq30
    | exact resolve eq30 eq2510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510
  have eq2562 : x = y ∨ x = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2515
    | exact resolve eq2515 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515
  have eq2563 : x = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2562
  have eq2567 : x = (τ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2563 eq29
    | exact resolve eq29 eq2563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq3399 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq941 eq2322
    | exact resolve eq2322 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq2322
  have eq3426 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq3399 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399
  have eq3468 : ∀ X0 : G, x = (M.op x X0) ∨ x = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2563 eq3426
    | exact resolve eq3426 eq2563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563 eq3426
  have eq3505 : ∀ X0 : G, x = (M.op x X0) ∨ x = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq3468 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq4473 : x = (M.op x y) ∨ x = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19
       have i₂ := eq3505 y
       grind)
    | exact superpose eq3505 eq19
    | (have j1 := eq3505 y
       grind)
    | exact resolve eq19 eq3505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505
  have eq4497 : x = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4473
  have eq4516 : y = (τ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4497 eq30
    | exact resolve eq30 eq4497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4497
  have eq4739 : x = y ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2567
       have i₂ := eq4516
       grind)
    | exact superpose eq4516 eq2567
    | exact resolve eq2567 eq4516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567 eq4516
  have eq4771 : x = (M.op x y) ∨ x = y := by grind
  clear eq4739
  have eq4784 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq4771 eq21
    | exact resolve eq21 eq4771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4800 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4771 eq382
    | exact resolve eq382 eq4771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq4801 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq4771 eq421
    | exact resolve eq421 eq4771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq4771
  have eq4819 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq4801
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4801
    | exact resolve eq4801 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4801
  have eq4820 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4800 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4800
    | (have j0 := eq4800 X0
       grind)
    | exact resolve eq4800 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4800
  have eq4835 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq4784
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4784
    | exact resolve eq4784 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq4839 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21 eq4819
    | exact resolve eq4819 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4819
  have eq4843 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4835 eq27
    | exact resolve eq27 eq4835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835
  have eq5645 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq4839 eq4843
    | exact resolve eq4843 eq4839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4843
  have eq5660 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by grind
  clear eq5645
  have eq6331 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq5660 eq4820
    | exact resolve eq4820 eq5660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4820 eq5660
  have eq6336 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq6331
  have eq6348 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq6336 eq28
    | exact resolve eq28 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6336
  have eq6370 : x = y := by
    first
    | (have r₁ := eq6348
       have r₂ := eq4839
       grind)
    | exact resolve eq6348 eq4839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4839 eq6348
  have eq6371 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq6370
       grind)
    | exact superpose eq6370 eq19
    | exact resolve eq19 eq6370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq6372 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq6370
       grind)
    | exact superpose eq6370 eq25
    | exact resolve eq25 eq6370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq6370
  have eq6408 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq6372
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6372
    | exact resolve eq6372 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6372
  have eq6597 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6408 eq27
    | exact resolve eq27 eq6408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6408
  have eq6701 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6597 eq73
    | exact resolve eq73 eq6597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq6597
  have eq6722 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6701
       have i₂ := eq6371
       grind)
    | exact superpose eq6371 eq6701
    | exact resolve eq6701 eq6371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6371 eq6701
  have eq7066 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6722 eq15
    | exact resolve eq15 eq6722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6722
  have eq7112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq7066
    | exact resolve eq7066 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq7066
  have eq7121 : False := by grind
  exact eq7121

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
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
  have eq179 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq16 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op X2 (M.op X1 X2))) X1
       have r₂ := eq16 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq179 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq181 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 X1 X2
       have i₂ := eq16 X2 X0 X1
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq745 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq783 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq786 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq745 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq795 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq786 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq786 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq786 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq797 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq784 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq784
    | (have j0 := eq784 (σ X0)
       grind)
    | exact resolve eq784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op X2 (M.op X1 X2)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq181 X1 X2 (τ X0)
       grind)
    | exact superpose eq181 eq39
    | exact resolve eq39 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq181
  have eq857 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 (M.op X2 (M.op X1 X2)))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq843 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq843
    | exact resolve eq843 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1467 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (k (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X2) = (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq795 (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X2
       have i₂ := eq857 (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X0 X1
       grind)
    | exact superpose eq857 eq795
    | (have j0 := eq795 (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X2
       grind)
    | (have r₁ := eq795 (σ (M.op X1 (M.op X2 (M.op X1 X2)))) X1
       have r₂ := eq857 (σ (M.op X1 (M.op X2 (M.op X1 X2)))) X1 X2
       grind)
    | exact resolve eq795 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq1478 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X2) = (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1467 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1488 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1478 X0 X1 X2
       have i₂ := eq857 X2 X0 X1
       grind)
    | exact superpose eq857 eq1478
    | exact resolve eq1478 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq2108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq746
       grind)
    | exact superpose eq746 eq41
    | exact resolve eq41 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq746
  have eq2109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2108
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2108
    | exact resolve eq2108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108
  have eq2111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2109
    | exact resolve eq2109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq33080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2111 eq763
    | exact resolve eq763 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq2111
  have eq33088 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq33080
       have r₂ := eq27
       grind)
    | exact resolve eq33080 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33080
  have eq33516 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq33088 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq33088
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq33088
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq33088
       grind)
    | exact resolve eq13 eq33088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33553 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq33516 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33516
  have eq33701 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq33553 eq33088
    | exact resolve eq33088 eq33553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33088 eq33553
  have eq33702 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq33701
  have eq33758 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq33702 eq153
    | exact resolve eq153 eq33702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq33702
  have eq33769 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq32 eq33758
    | exact resolve eq33758 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq33758
  have eq33774 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq784 (σ x)
       grind)
    | (have r₁ := eq33769
       have r₂ := eq784 y
       grind)
    | exact resolve eq33769 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33769
  have eq33780 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq33774 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq33774
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq33774
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq33774
       grind)
    | exact resolve eq13 eq33774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33817 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq33780 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33780
  have eq33962 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq33817 eq33774
    | exact resolve eq33774 eq33817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33774 eq33817
  have eq33963 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq33962
  have eq34008 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq33963 eq142
    | exact resolve eq142 eq33963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq33963
  have eq34019 : x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq34008
    | exact resolve eq34008 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34008
  have eq34024 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq784 y
       grind)
    | (have r₁ := eq34019
       have r₂ := eq784 x
       grind)
    | exact resolve eq34019 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq34019
  have eq34030 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq34024
       grind)
    | exact superpose eq34024 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq34024
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq34024
       grind)
    | exact resolve eq13 eq34024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34041 : ∀ X0 : G, (k (σ (M.op y (M.op y y))) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq857 X0 y y
       have i₂ := eq34024
       grind)
    | exact superpose eq34024 eq857
    | exact resolve eq857 eq34024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq34067 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq34030 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34030
  have eq34095 : ∀ X0 : G, (k (σ (M.op y y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq34024 eq34041
    | exact resolve eq34041 eq34024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34041
  have eq34132 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq34024 eq34095
    | exact resolve eq34095 eq34024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34024 eq34095
  have eq34154 : ∀ X0 : G, x = (M.op x x) ∨ (k (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34132 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34132
    | (have j0 := eq34132 X0
       grind)
    | exact resolve eq34132 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34132
  have eq35410 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq34067 x
       grind)
    | exact superpose eq34067 eq18
    | (have j1 := eq34067 x
       grind)
    | exact resolve eq18 eq34067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34067
  have eq35496 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq35410
       grind)
    | exact superpose eq35410 eq40
    | exact resolve eq40 eq35410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35410
  have eq35499 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35496
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35496
    | exact resolve eq35496 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35496
  have eq35503 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq35499
    | exact resolve eq35499 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35499
  have eq35507 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34154 eq35503
    | exact resolve eq35503 eq34154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34154 eq35503
  have eq35510 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq35507
       grind)
    | exact superpose eq35507 eq28
    | (have j0 := eq28 X0 x
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq35507
       grind)
    | exact resolve eq28 eq35507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35511 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq35507
       grind)
    | exact superpose eq35507 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq35507
       grind)
    | exact resolve eq13 eq35507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35548 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq35511 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35511
  have eq35549 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq35510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35510
  have eq35712 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35507
       have i₂ := eq35548 x
       grind)
    | exact superpose eq35548 eq35507
    | exact resolve eq35507 eq35548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35507 eq35548
  have eq35717 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq35712
  have eq35762 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq797 x
       have i₂ := eq35717
       grind)
    | exact superpose eq35717 eq797
    | (have j0 := eq797 x
       grind)
    | exact resolve eq797 eq35717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797 eq35717
  have eq35771 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq35762
  have eq35772 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35771
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35771
    | exact resolve eq35771 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35771
  have eq35781 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq35772 eq28
    | (have j0 := eq28 X0 (σ x)
       grind)
    | (have r₁ := eq28 X0 (σ x)
       have r₂ := eq35772
       grind)
    | exact resolve eq28 eq35772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq35772
  have eq35820 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq35781 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35781
  have eq37892 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35549 y
       grind)
    | exact superpose eq35549 eq18
    | (have j1 := eq35549 y
       grind)
    | exact resolve eq18 eq35549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35549
  have eq38490 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq37892
       grind)
    | exact superpose eq37892 eq40
    | exact resolve eq40 eq37892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq37892
  have eq38492 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq38490
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38490
    | exact resolve eq38490 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38490
  have eq38496 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq38492
    | exact resolve eq38492 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq38492
  have eq39533 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35820 eq26
    | (have j1 := eq35820 (σ y)
       grind)
    | exact resolve eq26 eq35820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35820
  have eq39902 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38496 eq39533
    | exact resolve eq39533 eq38496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38496 eq39533
  have eq40081 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq39902
       have r₂ := eq27
       grind)
    | exact resolve eq39902 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39902
  have eq40149 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq40081 eq29
    | exact resolve eq29 eq40081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq40281 : x = (M.op x y) := by
    first
    | exact superpose eq40149 eq30
    | exact resolve eq30 eq40149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq40149
  have eq40360 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq40281
       grind)
    | exact superpose eq40281 eq175
    | exact resolve eq175 eq40281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq40281
  have eq43124 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq40360 eq1488
    | exact resolve eq1488 eq40360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488 eq40360
  have eq43295 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq43124 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43124
    | (have j0 := eq43124 X0
       grind)
    | exact resolve eq43124 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq43124
  have eq45083 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43295 eq26
    | (have j1 := eq43295 (σ x)
       grind)
    | exact resolve eq26 eq43295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq43295
  have eq45149 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq45083 eq27
    | exact resolve eq27 eq45083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq45083
  have eq45290 : False := by grind
  exact eq45290

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation452 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq18 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq14 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq14 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13 (σ y) (σ x)
       grind)
    | exact superpose eq13 eq16
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq13 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq13 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19
    | exact resolve eq19 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22 : (M.op (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq20
  have eq23 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq21
  have eq24 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq22
    | exact resolve eq22 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq25 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq26 : (σ (k y y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq24
  have eq27 : (σ (k y y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq25
  have eq28 : (σ (k y y)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq26
    | exact resolve eq26 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq29 : (σ (k y y)) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq27
    | exact resolve eq27 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq33 : (k y y) = (τ (σ (k x x))) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq10
    | exact resolve eq10 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq36 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq33
    | exact resolve eq33 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : (σ (k x y)) ≠ (σ (k x y)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq36
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq36
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq36
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq36
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq36 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq41 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by grind
  clear eq39
  have eq43 : (k y y) = (M.op x x) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq41
  have eq45 : (k y y) = (k x x) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq43
  have eq46 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45
  have eq47 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq28
    | exact resolve eq28 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq48 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47
  have eq49 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq48
  have eq51 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x x) ≠ (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq49
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq49
       have r₂ := eq13 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq49
       have r₂ := eq13 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq49 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x x) ≠ (M.op y y) := by grind
  clear eq51
  have eq53 : (σ x) = (σ y) ∨ x = y ∨ (M.op x x) ≠ (M.op y y) := by grind
  clear eq52
  have eq55 : (k y y) ≠ (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq53
  have eq57 : (k y y) ≠ (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq55
  have eq59 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq57
       have r₂ := eq46
       grind)
    | exact resolve eq57 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq57
  have eq63 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq59
       grind)
    | exact superpose eq59 eq10
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq64 : x = y ∨ x = y := by
    first
    | (have i₁ := eq63
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : x = y := by grind
  clear eq64
  have eq70 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65
       grind)
    | exact superpose eq65 eq16
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq71 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq70
  have eq72 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq71
  have eq73 : False := by grind
  exact eq73

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_x_pxy_Equation452 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq99 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq95
  have eq100 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq99
  have eq121 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq124 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq121
  have eq125 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq124
  have eq164 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq383 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq719 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq662 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq662
    | (have j0 := eq662 x X0
       grind)
    | exact resolve eq662 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq2428 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq383 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq14 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq14 eq383
    | exact resolve eq383 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq2467 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2428 X0 X1 X2
       have i₂ := eq45 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq45 eq2428
    | exact resolve eq2428 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428
  have eq2483 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2467 X0 X1 X2
       have i₂ := eq14 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq14 eq2467
    | exact resolve eq2467 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467
  have eq2494 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2483 X0 X1 X2
       have i₂ := eq45 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq45 eq2483
    | exact resolve eq2483 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq2483
  have eq2501 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2494 X0 X1 X2
       have i₂ := eq14 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq14 eq2494
    | exact resolve eq2494 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq6406 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq719 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq719
    | (have j0 := eq719 y
       grind)
    | exact resolve eq719 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq6442 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6406
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq6406
    | exact resolve eq6406 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6406
  have eq6471 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq6442
    | exact resolve eq6442 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6442
  have eq6479 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6471
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq6471
    | exact resolve eq6471 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6471
  have eq6484 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq6479
    | exact resolve eq6479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6479
  have eq12081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq12081
    | exact resolve eq12081 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12081
  have eq12093 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq12082
       have r₂ := eq28
       grind)
    | exact resolve eq12082 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12082
  have eq12097 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq12093
    | exact resolve eq12093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12093
  have eq12108 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12097 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12097
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12097
       grind)
    | exact resolve eq12 eq12097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12097
  have eq16658 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq12108
    | (have j0 := eq12108 (σ x)
       grind)
    | (have r₁ := eq12108 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq12108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12108
  have eq16659 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq16658
  have eq16660 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq16659
  have eq16669 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq16660 eq89
    | exact resolve eq89 eq16660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq16660
  have eq16681 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16669
  have eq16701 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq16681
       grind)
    | exact superpose eq16681 eq100
    | exact resolve eq100 eq16681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq16710 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (k X0 y) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq16681
       grind)
    | exact superpose eq16681 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16681
       grind)
    | exact resolve eq12 eq16681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16681
  have eq16725 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq16701
    | exact resolve eq16701 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16701
  have eq96072 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16710 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16710
    | (have j0 := eq16710 x
       grind)
    | (have r₁ := eq16710 x
       have r₂ := eq19
       grind)
    | exact resolve eq16710 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16710
  have eq96073 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq96072
  have eq96074 : x = (k x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq96073
  have eq96077 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq96074
       grind)
    | exact superpose eq96074 eq49
    | exact resolve eq49 eq96074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq96074
  have eq96165 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96077
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96077
    | exact resolve eq96077 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96077
  have eq96210 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq96165 eq6484
    | exact resolve eq6484 eq96165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6484 eq96165
  have eq96264 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq96210
  have eq96710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq96264 eq16725
    | exact resolve eq16725 eq96264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96264
  have eq96823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq96710
  have eq96840 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq96823
       have r₂ := eq28
       grind)
    | exact resolve eq96823 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96823
  have eq96847 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq96840 eq54
    | exact resolve eq54 eq96840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq96840
  have eq98974 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f98974_16 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x y)) := by
      intro X0
      grind
    have f98974_22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
      intro X0 X1 X2
      grind
    have f98974_25 : X0 ≠ (M.op X0 (σ y)) := by grind
    have f98974_26 : x ≠ y := by grind
    have f98974_27 : (σ x) ≠ (σ y) := by grind
    have f98974_28 : (σ x) ≠ (σ (M.op x y)) := by grind
    have f98974_30 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x y)) := by
      intro X0
      first
      | (have j0 := f98974_16 X0
         grind)
      | (have r₁ := f98974_16 X0
         have r₂ := f98974_26
         grind)
      | exact resolve f98974_16 f98974_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f98974_31 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ (M.op x y)) := by
      intro X0
      first
      | (have j0 := f98974_30 X0
         grind)
      | (have r₁ := f98974_30 X0
         have r₂ := f98974_27
         grind)
      | exact resolve f98974_30 f98974_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f98974_32 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f98974_31 X0
         grind)
      | (have r₁ := f98974_31 X0
         have r₂ := f98974_28
         grind)
      | exact resolve f98974_31 f98974_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f98974_48 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f98974_22 X0 (σ y) (σ x)
         have i₂ := f98974_32 (σ y)
         grind)
      | exact superpose f98974_32 f98974_22
      | exact resolve f98974_22 f98974_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f98974_53 : X0 ≠ X0 := by
      first
      | (have i₁ := f98974_25
         have i₂ := f98974_48 X0
         grind)
      | exact superpose f98974_48 f98974_25
      | (have r₁ := f98974_25
         have r₂ := f98974_48 X0
         grind)
      | exact resolve f98974_25 f98974_48
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f98974_54 : False := by grind
    exact f98974_54
  clear eq96847
  have eq99132 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq98974 eq16725
    | exact resolve eq16725 eq98974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16725
  have eq99241 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq99132
  have eq99320 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq99241 eq30
    | exact resolve eq30 eq99241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99241
  have eq99457 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq99320
    | exact resolve eq99320 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99320
  have eq99458 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq99457
  have eq99479 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq99458 eq30
    | exact resolve eq30 eq99458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq99719 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq99458 eq98974
    | exact resolve eq98974 eq99458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98974 eq99458
  have eq99720 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq99719 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99719
  have eq99991 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq99479
    | exact resolve eq99479 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99479
  have eq100012 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq99991 eq29
    | exact resolve eq29 eq99991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99991
  have eq100307 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq100012
    | exact resolve eq100012 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100012
  have eq100328 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq100307 eq53
    | exact resolve eq53 eq100307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101465 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq99720 eq164
    | exact resolve eq164 eq99720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq99720
  have eq101501 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31 eq101465
    | exact resolve eq101465 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101465
  have eq101646 : y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq100307 eq101501
    | exact resolve eq101501 eq100307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101501
  have eq101683 : y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq101646
  have eq168724 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq100328 X0
       have i₂ := eq101683
       grind)
    | exact superpose eq101683 eq100328
    | exact resolve eq100328 eq101683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100328 eq101683
  have eq168786 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq168724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168724
  have eq168832 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq168786 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq168786
    | (have j0 := eq168786 X0
       grind)
    | exact resolve eq168786 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168786
  have eq169248 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq100307 eq168832
    | exact resolve eq168832 eq100307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100307 eq168832
  have eq169389 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq169248 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169248
  have eq169788 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq169389 x
       grind)
    | exact superpose eq169389 eq19
    | (have j1 := eq169389 x
       grind)
    | exact resolve eq19 eq169389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169389
  have eq169962 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq169788
  have eq170491 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq169962 eq29
    | exact resolve eq29 eq169962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq169962
  have eq170803 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq170491
    | exact resolve eq170491 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq170491
  have eq170804 : x = (M.op x y) ∨ x = y := by grind
  clear eq170803
  have eq170824 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq170804 eq21
    | exact resolve eq21 eq170804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170826 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq170804 eq53
    | exact resolve eq53 eq170804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq170804
  have eq171378 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq170824
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq170824
    | exact resolve eq170824 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170824
  have eq171409 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq171378 eq27
    | exact resolve eq27 eq171378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171378
  have eq177450 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2501 y x X0
       have i₂ := eq170826 y
       grind)
    | exact superpose eq170826 eq2501
    | exact resolve eq2501 eq170826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501 eq170826
  have eq177549 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq177450 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq177450
    | (have j0 := eq177450 X0
       grind)
    | exact resolve eq177450 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177450
  have eq177942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq177549 eq171409
    | exact resolve eq171409 eq177549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171409 eq177549
  have eq178127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq177942
  have eq178164 : x = y := by
    first
    | (have r₁ := eq178127
       have r₂ := eq28
       grind)
    | exact resolve eq178127 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178127
  have eq178207 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq178164
       grind)
    | exact superpose eq178164 eq19
    | exact resolve eq19 eq178164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq178208 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq178164
       grind)
    | exact superpose eq178164 eq25
    | exact resolve eq25 eq178164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq178164
  have eq178491 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq178208
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq178208
    | exact resolve eq178208 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq178208
  have eq178522 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq178491 eq27
    | exact resolve eq27 eq178491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq178491
  have eq178819 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178522 eq68
    | exact resolve eq68 eq178522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq178522
  have eq178852 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq178819
       have i₂ := eq178207
       grind)
    | exact superpose eq178207 eq178819
    | exact resolve eq178819 eq178207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178207 eq178819
  have eq178868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq178852 eq15
    | exact resolve eq15 eq178852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178852
  have eq179189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq178868
    | exact resolve eq178868 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq178868
  have eq179290 : False := by grind
  exact eq179290

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxy_pyy_pyx_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
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
  clear eq25
  have eq53 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X4) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X0 x x X4
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq112 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq113 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq58 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x y
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq53 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq374 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq220 eq353
    | exact resolve eq353 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq376 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq206 eq349
    | exact resolve eq349 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq390 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 x y X1 X2
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59
    | (have j0 := eq59 X0 X1 X2 x y
       grind)
    | exact resolve eq59 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq729 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq390 X0 x x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq390
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq390 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14014
    | exact resolve eq14014 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14014
  have eq14026 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14015
       have r₂ := eq28
       grind)
    | exact resolve eq14015 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14015
  have eq14028 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14026
    | exact resolve eq14026 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14026
  have eq14031 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14028 eq113
    | (have r₁ := eq113
       have r₂ := eq14028
       grind)
    | exact resolve eq113 eq14028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14059 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq14028
  have eq14061 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq14031
  have eq14119 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14061
       have r₂ := eq14059
       grind)
    | exact resolve eq14061 eq14059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14059 eq14061
  have eq14125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14119 eq98
    | exact resolve eq98 eq14119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14119
  have eq14134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq14125
  have eq14137 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq14134
       have r₂ := eq28
       grind)
    | exact resolve eq14134 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14134
  have eq14141 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq14137 eq374
    | exact resolve eq374 eq14137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14144 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  have eq14151 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq14137 eq58
    | exact resolve eq58 eq14137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14137
  have eq14173 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq220 eq14151
    | exact resolve eq14151 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14151
  have eq14180 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq14173
    | exact resolve eq14173 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq14470 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq14144 eq98
    | exact resolve eq98 eq14144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq14144
  have eq14480 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq14470
  have eq14484 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14480 eq14141
    | exact resolve eq14141 eq14480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14141 eq14480
  have eq14507 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq14484
  have eq14671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq14507 eq14180
    | exact resolve eq14180 eq14507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14180 eq14507
  have eq14702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq14671
  have eq14714 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14702
       have r₂ := eq28
       grind)
    | exact resolve eq14702 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14702
  have eq14720 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq14714
       grind)
    | exact superpose eq14714 eq112
    | (have r₁ := eq112
       have r₂ := eq14714
       grind)
    | exact resolve eq112 eq14714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq14745 : y ≠ (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq14714
  have eq14747 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by grind
  clear eq14720
  have eq14980 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14747
       have r₂ := eq14745
       grind)
    | exact resolve eq14747 eq14745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14745 eq14747
  have eq14982 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq14980
       grind)
    | exact superpose eq14980 eq77
    | exact resolve eq77 eq14980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14980
  have eq15002 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq14982
    | exact resolve eq14982 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14982
  have eq15017 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15002 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq15002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15017
    | exact resolve eq15017 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15017
  have eq15033 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15022
       have r₂ := eq28
       grind)
    | exact resolve eq15022 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15022
  have eq15035 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15033
    | exact resolve eq15033 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15033
  have eq15641 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15035 eq113
    | (have r₁ := eq113
       have r₂ := eq15035
       grind)
    | exact resolve eq113 eq15035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15670 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq15035
  have eq15672 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq15641
  have eq17227 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq82 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq82
    | (have j0 := eq82 x
       grind)
    | exact resolve eq82 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq82
  have eq17277 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq17227
    | exact resolve eq17227 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17227
  have eq17291 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17277
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq17277
    | exact resolve eq17277 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17277
  have eq17294 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq17291
    | exact resolve eq17291 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17291
  have eq34314 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15672
       have r₂ := eq15670
       grind)
    | exact resolve eq15672 eq15670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15670 eq15672
  have eq34338 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34314 eq15002
    | exact resolve eq15002 eq34314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34314
  have eq34373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq34338
  have eq34388 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq34373
       have r₂ := eq28
       grind)
    | exact resolve eq34373 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34373
  have eq34396 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34388 eq374
    | exact resolve eq374 eq34388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq34399 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  have eq34406 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34388 eq58
    | exact resolve eq58 eq34388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34388
  have eq34438 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq220 eq34406
    | exact resolve eq34406 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34406
  have eq34445 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq34438
    | exact resolve eq34438 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34438
  have eq34654 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34399 eq15002
    | exact resolve eq15002 eq34399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15002 eq34399
  have eq34691 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq34654
  have eq34708 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34691 eq34396
    | exact resolve eq34396 eq34691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34396 eq34691
  have eq34740 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq34708
  have eq34762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq34740 eq34445
    | exact resolve eq34445 eq34740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34445 eq34740
  have eq34804 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq34762
  have eq34820 : y = (M.op x x) := by
    first
    | (have r₁ := eq34804
       have r₂ := eq28
       grind)
    | exact resolve eq34804 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34804
  have eq34830 : (M.op y x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq376 x
       have i₂ := eq34820
       grind)
    | exact superpose eq34820 eq376
    | exact resolve eq376 eq34820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq34832 : (k y x) = (M.op y x) := by grind
  have eq34838 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq34820
       grind)
    | exact superpose eq34820 eq57
    | exact resolve eq57 eq34820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq34842 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq390 X0 x x
       have i₂ := eq34820
       grind)
    | exact superpose eq34820 eq390
    | exact resolve eq390 eq34820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq34820
  have eq34872 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq206 eq34838
    | exact resolve eq34838 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq34838
  have eq34884 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq34872
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34872
    | exact resolve eq34872 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq34872
  have eq35341 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq34884 eq34830
    | exact resolve eq34830 eq34884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34830 eq34884
  have eq35402 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq34832
       have i₂ := eq35341
       grind)
    | exact superpose eq35341 eq34832
    | exact resolve eq34832 eq35341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34832 eq35341
  have eq35405 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq35402
       grind)
    | exact superpose eq35402 eq77
    | exact resolve eq77 eq35402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq35402
  have eq35424 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq35405
    | exact resolve eq35405 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq35405
  have eq35445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35424 eq17294
    | exact resolve eq17294 eq35424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17294
  have eq35450 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq35445
       have r₂ := eq28
       grind)
    | exact resolve eq35445 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35445
  have eq52759 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35450 eq113
    | (have r₁ := eq113
       have r₂ := eq35450
       grind)
    | exact resolve eq113 eq35450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq52800 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq35450
  have eq52802 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq52759
  have eq52827 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35424 eq52802
    | exact resolve eq52802 eq35424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52802
  have eq52844 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq52827
       have r₂ := eq28
       grind)
    | exact resolve eq52827 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52827
  have eq53221 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq52844
       have r₂ := eq52800
       grind)
    | exact resolve eq52844 eq52800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52800 eq52844
  have eq53231 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by grind
  have eq53238 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq53221 eq58
    | exact resolve eq58 eq53221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq53242 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq53221 eq729
    | exact resolve eq729 eq53221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq53221
  have eq53283 : (M.op (σ y) (σ x)) = (M.op (σ x) y) := by
    first
    | exact superpose eq34842 eq53242
    | exact resolve eq53242 eq34842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53242
  have eq53287 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq220 eq53238
    | exact resolve eq53238 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq53238
  have eq53293 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq35424 eq53231
    | exact resolve eq53231 eq35424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35424 eq53231
  have eq53316 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq34842 eq53287
    | exact resolve eq53287 eq34842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34842 eq53287
  have eq53328 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq27 eq53316
    | exact resolve eq53316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq53316
  have eq56830 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq53328 eq53283
    | exact resolve eq53283 eq53328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53283 eq53328
  have eq56831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53293 eq56830
    | exact resolve eq56830 eq53293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53293 eq56830
  have eq56832 : False := by grind
  exact eq56832

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pxx_pxy_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq181 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 X1 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X0 X1 X2 x
       have i₂ := eq16 X0 X3 X4 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq181 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq181
    | (have j0 := eq181 x y
       grind)
    | exact resolve eq181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X1 X2 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq183
    | (have j0 := eq183 X0 X1 X2 x y
       grind)
    | exact resolve eq183 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq970 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op x y)) := by
    intro X0 X3
    first
    | (have i₁ := eq16 X0 x x X3
       have i₂ := eq842 X0 x x
       grind)
    | (have i₁ := eq16 X0 x y X3
       have i₂ := eq842 X0 x x
       grind)
    | exact superpose eq842 eq16
    | (have j0 := eq16 X0 x y X3
       grind)
    | exact resolve eq16 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1078 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq1088 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1092 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1575 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1078
       grind)
    | exact superpose eq1078 eq41
    | exact resolve eq41 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1576 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1575
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1575
    | exact resolve eq1575 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq1578 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1576
    | exact resolve eq1576 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576
  have eq1588 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1578 eq1088
    | exact resolve eq1088 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088 eq1578
  have eq1595 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1588
       have r₂ := eq27
       grind)
    | exact resolve eq1588 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1601 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1595 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1595
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1595
       grind)
    | exact resolve eq13 eq1595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1924 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq1601 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1925 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1595 eq1924
    | exact resolve eq1924 eq1595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595 eq1924
  have eq1928 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1925 eq153
    | exact resolve eq153 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1925
  have eq1931 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq1928
    | exact resolve eq1928 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928
  have eq1934 : y = (M.op y y) := by
    first
    | (have j1 := eq1092 y
       grind)
    | (have r₁ := eq1931
       have r₂ := eq1092 y
       grind)
    | exact resolve eq1931 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq1938 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq12
    | (have j0 := eq12 (k X0 y) X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq1934
       grind)
    | exact resolve eq12 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1943 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq181 y y
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq181
    | exact resolve eq181 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1948 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq842 X0 y y
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq842
    | exact resolve eq842 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1950 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq970 y y
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq970
    | exact resolve eq970 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1951 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq1938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq1952 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1950
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq1950
    | exact resolve eq1950 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950
  have eq1957 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1943
       have i₂ := eq1948 sF0
       grind)
    | exact superpose eq1948 eq1943
    | exact resolve eq1943 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq1962 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1957
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1957
    | exact resolve eq1957 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq2030 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1948 x
       grind)
    | exact superpose eq1948 eq18
    | (have j1 := eq1948 x
       grind)
    | exact resolve eq18 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2125 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (k X0 y) X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq970 X0 X0
       have i₂ := eq1951 X0
       grind)
    | exact superpose eq1951 eq970
    | (have j1 := eq1951 X0
       grind)
    | exact resolve eq970 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2220 : ∀ X0 : G, (M.op (k X0 y) X0) = (k (k X0 y) X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq1951 X0
       grind)
    | exact superpose eq1951 eq186
    | (have j1 := eq1951 X0
       grind)
    | exact resolve eq186 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq2230 : (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq186 y
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq186
    | exact resolve eq186 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2309 : y = (k y y) := by
    first
    | (have i₁ := eq2230
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq2230
    | exact resolve eq2230 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934 eq2230
  have eq2317 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (k X0 y) X0) ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq2125 eq2220
    | (have j0 := eq2220 X0
       have j1 := eq2125 X0
       grind)
    | exact resolve eq2220 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125 eq2220
  have eq3426 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2309
       grind)
    | exact superpose eq2309 eq41
    | exact resolve eq41 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309
  have eq3429 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3426
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3426
    | exact resolve eq3426 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426
  have eq3440 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3429 eq1092
    | (have j0 := eq1092 (σ y)
       grind)
    | (have r₁ := eq1092 (σ y)
       have r₂ := eq3429
       grind)
    | exact resolve eq1092 eq3429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq3429
  have eq3441 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3440
  have eq3459 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq3441 eq12
    | (have j0 := eq12 (k X0 (σ y)) X0
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq3441
       grind)
    | exact resolve eq12 eq3441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3471 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq3441 eq842
    | exact resolve eq842 eq3441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq3473 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op x y)) := by
    first
    | exact superpose eq3441 eq970
    | exact resolve eq970 eq3441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3474 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have j0 := eq3459 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3459
  have eq3475 : (σ y) = (M.op (σ y) (M.op x y)) := by
    first
    | exact superpose eq3441 eq3473
    | exact resolve eq3473 eq3441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3441 eq3473
  have eq3668 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq3471 eq26
    | (have j1 := eq3471 (σ x)
       grind)
    | exact resolve eq26 eq3471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3471
  have eq8589 : ∀ X0 : G, (k (k X0 (σ y)) X0) = (M.op (k X0 (σ y)) X0) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq3474 X0
       grind)
    | exact superpose eq3474 eq186
    | (have j1 := eq3474 X0
       grind)
    | exact resolve eq186 eq3474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq8614 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (k X0 (σ y)) X0) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq970 X0 X0
       have i₂ := eq3474 X0
       grind)
    | exact superpose eq3474 eq970
    | (have j1 := eq3474 X0
       grind)
    | exact resolve eq970 eq3474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq3474
  have eq8681 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (k X0 (σ y)) X0) ∨ (σ y) = X0 := by
    intro X0
    first
    | exact superpose eq8614 eq8589
    | (have j0 := eq8589 X0
       have j1 := eq8614 X0
       grind)
    | exact resolve eq8589 eq8614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8589 eq8614
  have eq22268 : (σ (M.op x (M.op x y))) = (k (σ (k x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 (k x y)
       have i₂ := eq2317 x
       grind)
    | exact superpose eq2317 eq40
    | (have j1 := eq2317 x
       grind)
    | exact resolve eq40 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2317
  have eq22288 : (σ (M.op x (M.op x y))) = (k (k (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq22268
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq22268
    | exact resolve eq22268 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq22268
  have eq22322 : (k (k (σ x) (σ y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq22288
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22288
    | exact resolve eq22288 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22288
  have eq22345 : (k (k (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) y)) ∨ x = y := by
    first
    | exact superpose eq189 eq22322
    | exact resolve eq22322 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq22322
  have eq22360 : (k (k (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq22345
       have i₂ := eq1948 sF0
       grind)
    | exact superpose eq1948 eq22345
    | exact resolve eq22345 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948 eq22345
  have eq22365 : (σ (M.op x y)) = (k (k (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq1962 eq22360
    | exact resolve eq22360 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962 eq22360
  have eq22367 : (σ (M.op x y)) = (k (k (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq22365
    | exact resolve eq22365 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22365
  have eq38010 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8681 eq22367
    | (have j1 := eq8681 (σ x)
       grind)
    | exact resolve eq22367 eq8681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8681 eq22367
  have eq38055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3668 eq38010
    | exact resolve eq38010 eq3668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38010
  have eq38097 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq38055
       have r₂ := eq27
       grind)
    | exact resolve eq38055 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38055
  have eq38143 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq38097 eq32
    | exact resolve eq32 eq38097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq38097
  have eq38287 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq38143
    | exact resolve eq38143 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq38143
  have eq38288 : x = y := by grind
  clear eq38287
  have eq38300 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38288
       grind)
    | exact superpose eq38288 eq24
    | exact resolve eq24 eq38288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq38310 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1952
       have i₂ := eq38288
       grind)
    | exact superpose eq38288 eq1952
    | exact resolve eq1952 eq38288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952 eq38288
  have eq38469 : x = (M.op x y) := by
    first
    | exact superpose eq2030 eq38310
    | exact resolve eq38310 eq2030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030 eq38310
  have eq38478 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq38300
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38300
    | exact resolve eq38300 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38300
  have eq38502 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq38469
       grind)
    | exact superpose eq38469 eq22
    | exact resolve eq22 eq38469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq38469
  have eq38606 : (σ x) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq38478 eq3475
    | exact resolve eq3475 eq38478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475 eq38478
  have eq38780 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38502 eq20
    | exact resolve eq20 eq38502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq38502
  have eq39251 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38606 eq3668
    | exact resolve eq3668 eq38606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668 eq38606
  have eq39447 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq39251 eq27
    | exact resolve eq27 eq39251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq39251
  have eq39705 : False := by grind
  exact eq39705
