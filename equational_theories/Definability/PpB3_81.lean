import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_y_pyx_y_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X0)) = (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X0) X2 X3
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq14 (M.op X1 X2) X1 X2
       have i₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X0 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X2 X0 X2
       have i₂ := eq14 X0 X2 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 X2) X0
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X3) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) X0) ≠ (M.op X2 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X0 (M.op X2 X2)) = (M.op (M.op X2 X2) (M.op X2 X2)) ∨ (M.op X2 X2) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X2 X2)
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq12 X0 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X2 X2)
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X2) (M.op X1 X2))
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq96
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq96 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq128 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq128
    | exact resolve eq128 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq131 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq130
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq130
    | exact resolve eq130 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq90
    | (have j0 := eq90 (σ y) (σ x)
       grind)
    | exact resolve eq90 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq200
    | exact resolve eq200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq204 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq201
       have r₂ := eq27
       grind)
    | exact resolve eq201 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq206 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq204
    | exact resolve eq204 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq208 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq206 eq27
    | exact resolve eq27 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq53 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq54 eq260
    | exact resolve eq260 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : (M.op (M.op x y) (σ x)) = (M.op (σ x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq206 eq432
    | exact resolve eq432 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq454 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X2 X2) X0 X3 X4
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X2) X0 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X0 X0) x X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq524 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op x y) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq450 eq14
    | exact resolve eq14 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq525 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54 eq524
    | exact resolve eq524 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq524
  have eq526 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq525 x
       have i₂ := eq51 sF0 sF2 x x
       grind)
    | (have i₁ := eq525 x
       have i₂ := eq51 sF0 X1 x sF2
       grind)
    | exact superpose eq51 eq525
    | exact resolve eq525 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq622 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op X3 X4) X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 X4 X2 X0
       have i₂ := eq51 X0 X0 (M.op X2 X2) X1
       grind)
    | (have i₁ := eq55 X3 X4 X2 X0
       have i₂ := eq51 X0 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq763 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X4 X4) X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X4 X2 X0 X3
       have i₂ := eq51 X0 X0 (M.op X2 X3) X1
       grind)
    | (have i₁ := eq56 X4 X2 X0 X3
       have i₂ := eq51 X0 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq56
  have eq1147 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq113 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1429 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) ≠ (M.op X2 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X2) = (k X2 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (M.op X0 X0) X0 X2
       have i₂ := eq50 X0 (M.op X0 X0) (M.op X0 X0) X1
       grind)
    | exact superpose eq50 eq69
    | (have j0 := eq69 (M.op X0 X0) X1 X2
       grind)
    | (have r₁ := eq69 (M.op X0 X0) x (M.op (M.op (M.op X0 X0) X1) X0)
       have r₂ := eq50 X0 X1 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact resolve eq69 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq69
  have eq1596 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq11726 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq454 X0 X1 X2 X3 x
       have i₂ := eq458 X2 X3 x
       grind)
    | exact superpose eq458 eq454
    | exact resolve eq454 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq458
  have eq14233 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X2) X0) = (M.op (M.op X0 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq622 X0 X1 X2 x x
       have i₂ := eq11726 x x X2 X0
       grind)
    | (have i₁ := eq622 x X1 X2 x y
       have i₂ := eq11726 X0 X1 X2 x
       grind)
    | exact superpose eq11726 eq622
    | (have j0 := eq622 X0 X1 X2 x y
       grind)
    | exact resolve eq622 eq11726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq15859 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) X2) X0) = (M.op (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq763 X0 X1 X2 X3 x
       have i₂ := eq11726 x x X2 X0
       grind)
    | exact superpose eq11726 eq763
    | exact resolve eq763 eq11726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq82285 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) ≠ (M.op X2 (M.op (M.op (M.op x y) X0) X0)) ∨ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X2) = (k X2 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1429 X0 X1 X2
       have i₂ := eq14233 X0 X0 X0
       grind)
    | exact superpose eq14233 eq1429
    | (have j0 := eq1429 X0 X1 X2
       grind)
    | exact resolve eq1429 eq14233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq82286 : ∀ X0 X2 : G, (M.op X2 (M.op (M.op (M.op x y) X0) X0)) ≠ (M.op (M.op (M.op x y) X0) (M.op X0 X0)) ∨ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X2) = (k X2 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq82285 X0 x X2
       have i₂ := eq14233 (M.op X0 X0) x X0
       grind)
    | exact superpose eq14233 eq82285
    | (have j0 := eq82285 X0 x X2
       grind)
    | exact resolve eq82285 eq14233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82285
  have eq82287 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) ≠ (M.op X2 (M.op (M.op (M.op x y) X0) X0)) ∨ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X2) = (k X2 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq82286 X2 X2
       have i₂ := eq14233 sF0 X2 X2
       grind)
    | exact superpose eq14233 eq82286
    | (have j0 := eq82286 X0 X2
       grind)
    | exact resolve eq82286 eq14233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82286
  have eq82288 : ∀ X0 X2 : G, (M.op (M.op (M.op (M.op x y) X0) X0) X2) = (k X2 (M.op (M.op (M.op x y) X0) X0)) ∨ (M.op (M.op (M.op x y) X0) (M.op x y)) ≠ (M.op X2 (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq82287 X2 X2
       have i₂ := eq14233 X2 X2 X2
       grind)
    | exact superpose eq14233 eq82287
    | (have j0 := eq82287 X0 X2
       grind)
    | exact resolve eq82287 eq14233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82287
  have eq82289 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) ≠ (M.op X2 (M.op (M.op (M.op x y) X0) X0)) ∨ (M.op (M.op (M.op x y) X0) X2) = (k X2 (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq82288 X2 x
       have i₂ := eq11726 sF0 X2 X2 x
       grind)
    | exact superpose eq11726 eq82288
    | (have j0 := eq82288 X0 X2
       grind)
    | exact resolve eq82288 eq11726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11726 eq82288
  have eq92615 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1596 X0 X1
       have i₂ := eq14233 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14233 eq1596
    | (have j0 := eq1596 X0 X1
       grind)
    | exact resolve eq1596 eq14233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596 eq14233
  have eq92616 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq92615 x x
       have i₂ := eq15859 sF0 (M.op x x) x x
       grind)
    | exact superpose eq15859 eq92615
    | (have j0 := eq92615 X0 X1
       grind)
    | exact resolve eq92615 eq15859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92615
  have eq92617 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op X0 (M.op (M.op (M.op x y) X0) X0)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq92616 X0 X1
       have i₂ := eq15859 X0 X1 X0 X1
       grind)
    | (have i₁ := eq92616 (M.op x y) x
       have i₂ := eq15859 (M.op (M.op x y) x) X1 x x
       grind)
    | exact superpose eq15859 eq92616
    | (have j0 := eq92616 X0 X1
       grind)
    | exact resolve eq92616 eq15859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92616
  have eq92618 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) X0) = (k X0 (M.op (M.op (M.op x y) X0) X0)) ∨ (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op X0 (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq92617 (M.op x y) x
       have i₂ := eq15859 (M.op (M.op x y) x) x x x
       grind)
    | (have i₁ := eq92617 x x
       have i₂ := eq15859 x x x x
       grind)
    | exact superpose eq15859 eq92617
    | (have j0 := eq92617 X0 x
       grind)
    | exact resolve eq92617 eq15859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15859 eq92617
  have eq92619 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) X0) = (k X0 (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have j0 := eq92618 X0
       have j1 := eq82289 X0 X0
       grind)
    | (have r₁ := eq92618 x
       have r₂ := eq82289 x x
       grind)
    | exact resolve eq92618 eq82289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82289 eq92618
  have eq92666 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq526 eq92619
    | exact resolve eq92619 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq92774 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq206 eq92666
    | exact resolve eq92666 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92666
  have eq93068 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq92774 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92774
  have eq93236 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq93068
    | (have j0 := eq93068 (σ y)
       grind)
    | exact resolve eq93068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93068
  have eq93431 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq206 eq93236
    | exact resolve eq93236 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq93236
  have eq93445 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq93431
  have eq93559 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq93445 eq131
    | exact resolve eq131 eq93445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq93445
  have eq93572 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq93559
  have eq93577 : x = (M.op x y) := by
    first
    | (have r₁ := eq93572
       have r₂ := eq208
       grind)
    | exact resolve eq93572 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq93572
  have eq94020 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq93577 eq20
    | exact resolve eq20 eq93577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq94074 : ∀ X0 : G, (M.op (M.op x X0) X0) = (k X0 (M.op (M.op x X0) X0)) := by
    intro X0
    first
    | exact superpose eq93577 eq92619
    | exact resolve eq92619 eq93577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92619
  have eq94076 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq94074 x
       have i₂ := eq260 x x
       grind)
    | (have i₁ := eq94074 y
       have i₂ := eq260 X0 y
       grind)
    | exact superpose eq260 eq94074
    | exact resolve eq94074 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq94074
  have eq94120 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq94020
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94020
    | exact resolve eq94020 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94020
  have eq94121 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq93577 eq94076
    | exact resolve eq94076 eq93577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94076
  have eq94874 : (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq94121 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94121
    | (have j0 := eq94121 y
       grind)
    | exact resolve eq94121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq94121
  have eq94913 : x = (k y x) := by
    first
    | exact superpose eq93577 eq94874
    | exact resolve eq94874 eq93577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93577 eq94874
  have eq94946 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1147 x y
       have i₂ := eq94913
       grind)
    | exact superpose eq94913 eq1147
    | (have j0 := eq1147 x y
       grind)
    | exact resolve eq1147 eq94913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147 eq94913
  have eq94953 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq94946
  have eq94964 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq94953
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq94953
    | exact resolve eq94953 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq94953
  have eq94975 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq94964
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94964
    | exact resolve eq94964 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq94964
  have eq94984 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq94975
    | exact resolve eq94975 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq94975
  have eq94993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq94120 eq94984
    | exact resolve eq94984 eq94120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94120 eq94984
  have eq95001 : False := by grind
  exact eq95001

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq30 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq30 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq50 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq50 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq56
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq66 X0 X1
       have r₂ := eq65 X0 X1
       grind)
    | exact resolve eq66 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq66
  have eq162 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq166 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq162 X1 X1
       have r₂ := eq68 X1 X1
       grind)
    | (have r₁ := eq162 X1 X0
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq162 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq162
  have eq642 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq166 (σ X1) (σ X0)
       grind)
    | exact superpose eq166 eq15
    | exact resolve eq15 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq642 X0 X1
       have i₂ := eq166 X1 X0
       grind)
    | exact superpose eq166 eq642
    | exact resolve eq642 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq642
  have eq653 : False := by grind
  exact eq653

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyx_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq30 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq30 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq50 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq61
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq68 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq68 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq68
  have eq168 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq172 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       have j1 := eq70 X1 X0
       grind)
    | (have r₁ := eq168 X1 X1
       have r₂ := eq70 X1 X1
       grind)
    | (have r₁ := eq168 X1 X0
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq168 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq168
  have eq406 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq172 (σ X1) (σ X0)
       grind)
    | exact superpose eq172 eq15
    | exact resolve eq15 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq172 X1 X0
       grind)
    | exact superpose eq172 eq406
    | exact resolve eq406 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq406
  have eq414 : False := by grind
  exact eq414

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq48 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq48 (σ X0)
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq62
    | exact resolve eq62 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq62
  have eq85 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85
    | (have j0 := eq85 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq85 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq16
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq287
       have i₂ := eq85 y x
       grind)
    | exact superpose eq85 eq287
    | (have j1 := eq85 (σ x) (σ y)
       grind)
    | (have r₁ := eq287
       have r₂ := eq85 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq287
       have r₂ := eq85 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq287 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq287
  have eq654 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq651
  have eq655 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq654
       grind)
    | exact superpose eq654 eq16
    | exact resolve eq16 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq656 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq655
       have r₂ := eq71 x
       grind)
    | exact resolve eq655 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq695 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq656
       grind)
    | exact superpose eq656 eq10
    | exact resolve eq10 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq712 : x = y := by
    first
    | (have i₁ := eq695
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq695
    | exact resolve eq695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq759 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq712
       grind)
    | exact superpose eq712 eq16
    | exact resolve eq16 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq760 : False := by grind
  exact eq760

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq68 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq68 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq78 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq69 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq82 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq70 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq70 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq97 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       have j1 := eq73 X1 X0
       grind)
    | (have r₁ := eq78 X0 X1
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq78 X1 X0
       have r₂ := eq73 X0 X1
       grind)
    | exact resolve eq78 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq78
  have eq99 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq82
  have eq229 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq233 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq229 X0 X1
       have j1 := eq99 X1 X0
       grind)
    | (have r₁ := eq229 X1 X0
       have r₂ := eq99 X0 X1
       grind)
    | (have r₁ := eq229 X1 X1
       have r₂ := eq99 X1 X1
       grind)
    | exact resolve eq229 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq229
  have eq541 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq233 (σ X1) (σ X0)
       grind)
    | exact superpose eq233 eq15
    | exact resolve eq15 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1
       have i₂ := eq233 X1 X0
       grind)
    | exact superpose eq233 eq541
    | exact resolve eq541 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq541
  have eq550 : False := by grind
  exact eq550

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq123 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq123 (σ X0)
       grind)
    | exact superpose eq123 eq15
    | exact resolve eq15 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq126 X0
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq126
    | exact resolve eq126 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq126
  have eq2801 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2802 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2801 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2801
    | (have j0 := eq2801 (σ X0) (σ X1)
       grind)
    | exact resolve eq2801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6128 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2802 X1 X0
       have i₂ := eq2801 X1 X0
       grind)
    | exact superpose eq2801 eq2802
    | (have j0 := eq2802 X1 X0
       have j1 := eq2801 (σ X1) (σ X0)
       grind)
    | exact resolve eq2802 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39383 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6128 x y
       grind)
    | exact superpose eq6128 eq16
    | (have j1 := eq6128 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6128 x y
       grind)
    | exact resolve eq16 eq6128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6128
  have eq39501 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq39383
  have eq39563 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39501
       grind)
    | exact superpose eq39501 eq16
    | exact resolve eq16 eq39501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39565 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq39501
       grind)
    | exact superpose eq39501 eq12
    | exact resolve eq12 eq39501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39566 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq39501
       grind)
    | exact superpose eq39501 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq39501
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq39501
       grind)
    | exact resolve eq13 eq39501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39501
  have eq39627 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq39566
  have eq39632 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39627
       have i₂ := eq137 x
       grind)
    | exact superpose eq137 eq39627
    | exact resolve eq39627 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39627
  have eq39633 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39565
       have i₂ := eq137 x
       grind)
    | exact superpose eq137 eq39565
    | exact resolve eq39565 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq39565
  have eq39634 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39632
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq39632
    | exact resolve eq39632 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39632
  have eq39635 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39633
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq39633
    | exact resolve eq39633 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39633
  have eq39636 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2801 eq39634
    | (have j1 := eq2801 y x
       grind)
    | exact resolve eq39634 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39634
  have eq39637 : (σ (M.op x y)) = (σ y) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2801 eq39635
    | (have j1 := eq2801 y x
       grind)
    | exact resolve eq39635 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801 eq39635
  have eq39639 : y = (M.op x y) := by grind
  clear eq39563 eq39636 eq39637
  have eq39641 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39639
       grind)
    | exact superpose eq39639 eq16
    | exact resolve eq16 eq39639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39642 : y ≠ (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq39639
       grind)
    | exact superpose eq39639 eq12
    | exact resolve eq12 eq39639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39643 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq39639
       grind)
    | exact superpose eq39639 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq39639
       grind)
    | exact resolve eq13 eq39639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39639
  have eq39704 : y = (M.op x x) ∨ y = (k y x) := by grind
  clear eq39643
  have eq39705 : y = (k y x) := by
    first
    | (have r₁ := eq39642
       have r₂ := eq39704
       grind)
    | exact resolve eq39642 eq39704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39642 eq39704
  have eq39707 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2802 y x
       have i₂ := eq39705
       grind)
    | exact superpose eq39705 eq2802
    | (have j0 := eq2802 y x
       grind)
    | exact resolve eq2802 eq39705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802 eq39705
  have eq39710 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39707
  have eq39712 : False := by grind
  exact eq39712

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X2 X2) X0
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X2 X2) X0 X3 X4
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq62 (M.op X1 X2) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X4) X3) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X1 X2) X0 X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq62 (M.op X0 X0) X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X2 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq62 X1 X2 X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X0 X3) (M.op X0 X3)) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | (have i₁ := eq12 X2 (M.op X0 X3)
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq12
    | (have r₁ := eq12 (M.op X0 X3) (M.op X0 X3)
       have r₂ := eq62 X0 X3 (M.op X0 X3) X3
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq62 X0 X1 (M.op X0 X1) X1
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq123 (σ X0)
       grind)
    | exact superpose eq123 eq15
    | exact resolve eq15 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq123 (τ X0)
       grind)
    | exact superpose eq123 eq18
    | exact resolve eq18 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq133 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq130 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq130
    | exact resolve eq130 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq126 X0
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq126
    | exact resolve eq126 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq141 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq133
    | exact resolve eq133 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq133
  have eq148 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X1 X2 (σ X0) (σ X0)
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq71
    | exact resolve eq71 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ X0) X1 X2 (σ X0)
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq62
    | exact resolve eq62 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq141 X0
       grind)
    | exact superpose eq141 eq10
    | exact resolve eq10 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq433 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X4 X5) X2) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq64 X4 X5 X2 X3
       have i₂ := eq64 X0 X1 X2 X3
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X3 X3) (M.op X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq64 X0 X1 X4 X3
       have i₂ := eq62 (M.op X0 X1) X4 X3 X2
       grind)
    | (have i₁ := eq64 X0 X1 X4 X3
       have i₂ := eq62 (M.op X0 X1) X2 X3 X4
       grind)
    | exact superpose eq62 eq64
    | exact resolve eq64 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) ≠ (M.op (M.op (M.op X0 X1) X2) X2) ∨ (M.op (M.op X2 X2) X3) = (k X3 (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op X2 X2)
       have i₂ := eq64 X0 X1 X2 X2
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X3 (M.op X2 X2)
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       have r₂ := eq64 X0 X1 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq785 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X4 X4) X5) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq67 X2 X2 X4 X3 X5
       have i₂ := eq67 X0 X1 X2 X3 X4
       grind)
    | (have i₁ := eq67 X0 X1 X2 X3 X4
       have i₂ := eq67 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq67 eq67
    | exact resolve eq67 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X4 X4) X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq67 X2 X3 X4 X0 X5
       have i₂ := eq71 (M.op X2 X3) X4 X0 X1
       grind)
    | (have i₁ := eq67 X2 X3 X4 X0 X5
       have i₂ := eq71 X0 X1 (M.op X2 X3) X4
       grind)
    | exact superpose eq71 eq67
    | exact resolve eq67 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1167 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op X3 X4) X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq70 X2 X3 X4 X0 X5
       have i₂ := eq71 (M.op X2 X2) X3 X0 X1
       grind)
    | (have i₁ := eq70 X2 X3 X4 X0 X5
       have i₂ := eq71 X0 X1 (M.op X2 X2) X3
       grind)
    | exact superpose eq71 eq70
    | exact resolve eq70 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1786 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X5 X6) X4) X0) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq433 X2 X3 X4 X0 X5 X6
       have i₂ := eq71 (M.op X2 X3) X4 X0 X1
       grind)
    | (have i₁ := eq433 X2 X3 X4 X0 X5 X6
       have i₂ := eq71 X0 X1 (M.op X2 X3) X4
       grind)
    | exact superpose eq71 eq433
    | exact resolve eq433 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq2208 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ (M.op (M.op X3 X3) (M.op X3 X3)) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = (k (M.op X4 X4) (M.op X3 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X3 (M.op (M.op X0 X1) X2)
       have i₂ := eq462 X0 X1 X2 X3 X4
       grind)
    | (have i₁ := eq12 (M.op X4 X4) (M.op X3 X3)
       have i₂ := eq462 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq462 eq12
    | (have r₁ := eq12 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       have r₂ := eq462 X0 X1 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2238 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k (M.op X4 X4) (M.op X3 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq2208 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq2208 X0 X1 X2 X4 X4
       have r₂ := eq462 X0 X1 X2 X4 X4
       grind)
    | (have r₁ := eq2208 (M.op X1 X1) (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1) X4
       have r₂ := eq462 X1 X1 (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq2208 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq2208
  have eq2243 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq2245 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2243 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2243
    | (have j0 := eq2243 (σ X0) (σ X1)
       grind)
    | exact resolve eq2243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3459 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2245 X1 X0
       have i₂ := eq2243 X1 X0
       grind)
    | exact superpose eq2243 eq2245
    | (have j0 := eq2245 X1 X0
       have j1 := eq2243 (σ X1) (σ X0)
       grind)
    | exact resolve eq2245 eq2243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq5352 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X2) X3) X4) = (M.op (M.op (σ (M.op X0 X0)) X5) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq785 X1 X2 X3 X4 (σ X0) X5
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq785
    | exact resolve eq785 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq5699 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X2) (M.op X3 X4)) = (M.op (M.op (σ (M.op X0 X0)) X5) X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq787 X1 X2 X3 X4 (σ X0) X5
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq787
    | exact resolve eq787 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq6588 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X4) X5) X1) = (M.op (M.op X1 X2) (τ (M.op X0 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1167 X1 X2 (τ X0) X3 X4 X5
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq1167
    | exact resolve eq1167 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq8111 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) X4) = (k (σ (M.op X0 X0)) (M.op X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2238 X1 X2 X3 X4 (σ X0)
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq2238
    | exact resolve eq2238 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8114 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) X4) = (k (τ (M.op X0 X0)) (M.op X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2238 X1 X2 X3 X4 (τ X0)
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq2238
    | exact resolve eq2238 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29895 : ∀ X0 X1 X2 X6 : G, (M.op (M.op X0 X1) (τ (M.op X2 X2))) = (k (σ (M.op X6 X6)) (M.op X0 X0)) := by
    intro X0 X1 X2 X6
    first
    | (have i₁ := eq8111 X6 x x x X0
       have i₂ := eq6588 X2 X0 X1 x x x
       grind)
    | exact superpose eq6588 eq8111
    | exact resolve eq8111 eq6588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6588 eq8111
  have eq30326 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) (τ X0)) = (k (τ (M.op X4 X4)) (τ (M.op X0 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8114 X4 X1 X2 X3 (τ X0)
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq8114
    | exact resolve eq8114 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8114
  have eq30443 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) (τ X0)) = (τ (k (M.op X4 X4) (M.op X0 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30326 X0 X1 X2 X3 X4
       have i₂ := eq31 (M.op X0 X0) (M.op X4 X4)
       grind)
    | exact superpose eq31 eq30326
    | exact resolve eq30326 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq30326
  have eq35997 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3459 x y
       grind)
    | exact superpose eq3459 eq16
    | (have j1 := eq3459 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3459 x y
       grind)
    | exact resolve eq16 eq3459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3459
  have eq36140 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq35997
  have eq36243 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq150 x (σ y) X0
       have i₂ := eq36140
       grind)
    | exact superpose eq36140 eq150
    | exact resolve eq150 eq36140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36245 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) X1) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ x) (σ y) X0 X1
       have i₂ := eq36140
       grind)
    | exact superpose eq36140 eq62
    | exact resolve eq62 eq36140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36247 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X0 X1) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (σ x) (σ y) X0 X1
       have i₂ := eq36140
       grind)
    | exact superpose eq36140 eq71
    | exact resolve eq71 eq36140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36620 : ∀ X0 X2 X3 : G, (k (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (σ x) X0) X2) ∨ x = (M.op x y) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2238 (σ x) x X0 X2 X3
       have i₂ := eq36245 X0 x
       grind)
    | exact superpose eq36245 eq2238
    | exact resolve eq2238 eq36245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq36833 : ∀ X2 X3 : G, (k (M.op X3 X3) (M.op X2 X2)) = (M.op (σ x) X2) ∨ x = (M.op x y) := by
    intro X2 X3
    first
    | exact superpose eq36245 eq36620
    | exact resolve eq36620 eq36245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36620
  have eq36920 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq36247 (σ (M.op x x)) X0
       have i₂ := eq36243 X0
       grind)
    | exact superpose eq36243 eq36247
    | exact resolve eq36247 eq36243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37072 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36920 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36920
  have eq37107 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36247 eq37072
    | exact resolve eq37072 eq36247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36247 eq37072
  have eq37121 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37107
       have i₂ := eq137 x
       grind)
    | exact superpose eq137 eq37107
    | exact resolve eq37107 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37107
  have eq37283 : ∀ X0 X1 X2 X3 X5 X6 X7 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ (M.op (M.op X3 X7) (M.op X3 X7)) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = (k (M.op X5 X6) (M.op X3 X7)) := by
    intro X0 X1 X2 X3 X5 X6 X7
    first
    | (have i₁ := eq117 X0 X1 (M.op X2 X3) X3
       have i₂ := eq1786 X0 X1 X2 X3 x X5 X6
       grind)
    | (have i₁ := eq117 (M.op X5 X6) x X0 X3
       have i₂ := eq1786 X0 X1 X2 X3 x X5 X6
       grind)
    | exact superpose eq1786 eq117
    | (have r₁ := eq117 (M.op X5 X6) x (M.op X5 X6) X3
       have r₂ := eq1786 (M.op X5 X6) X3 (M.op X5 X6) X3 x X5 X6
       grind)
    | exact resolve eq117 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq37472 : ∀ X0 X1 X2 X3 X5 X6 X7 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k (M.op X5 X6) (M.op X3 X7)) := by
    intro X0 X1 X2 X3 X5 X6 X7
    first
    | (have j0 := eq37283 X0 X1 X2 X3 X5 X6 X7
       grind)
    | (have r₁ := eq37283 (M.op X5 X6) X1 X1 (M.op X5 X6) X5 X6 X1
       have r₂ := eq1786 (M.op (M.op X5 X6) X1) X1 X5 X6 X1 X5 X6
       grind)
    | (have r₁ := eq37283 X5 X6 x X2 X5 X6 X3
       have r₂ := eq1786 X2 X3 X2 X3 x X5 X6
       grind)
    | exact resolve eq37283 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786 eq37283
  have eq39337 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op (M.op (M.op X0 X1) X2) X2) ∨ (M.op (M.op X2 X2) X3) = (k X3 (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2243 eq479
    | (have j0 := eq479 X0 X1 X2 X3
       have j1 := eq2243 X3 (M.op X2 X2)
       grind)
    | (have r₁ := eq479 X0 X0 X0 X0
       have r₂ := eq2243 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq479 eq2243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq2243
  have eq163751 : ∀ X0 X1 X2 : G, (τ (k (M.op X2 X2) (M.op X1 X1))) = (M.op (M.op (σ (M.op x x)) X0) (τ X1)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30443 X1 (σ x) (σ (M.op x x)) X0 X2
       have i₂ := eq37121
       grind)
    | exact superpose eq37121 eq30443
    | exact resolve eq30443 eq37121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30443 eq37121
  have eq163801 : ∀ X0 X1 X2 : G, (τ (k (M.op X2 X2) (M.op X1 X1))) = (M.op (M.op (σ x) X0) (τ X1)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f163801_12 : ∀ X0 X1 X2 : G, (τ (k (M.op X2 X2) (M.op X1 X1))) = (M.op (M.op (σ (M.op x x)) X0) (τ X1)) ∨ x = (M.op x y) := by
      intro X0 X1 X2
      grind
    have f163801_13 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f163801_14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
      intro X0 X1 X2
      grind
    have f163801_21 : (τ (k (M.op X2 X2) (M.op X1 X1))) ≠ (M.op (M.op (σ x) X0) (τ X1)) := by grind
    have f163801_22 : x ≠ (M.op x y) := by grind
    have f163801_23 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ x) X0) := by
      intro X0
      first
      | (have j0 := f163801_13 X0
         grind)
      | (have r₁ := f163801_13 X0
         have r₂ := f163801_22
         grind)
      | exact resolve f163801_13 f163801_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f163801_24 : ∀ X0 X1 X2 : G, (τ (k (M.op X2 X2) (M.op X1 X1))) = (M.op (M.op (σ (M.op x x)) X0) (τ X1)) := by
      intro X0 X1 X2
      first
      | (have j0 := f163801_12 X0 X1 X2
         grind)
      | (have r₁ := f163801_12 X0 X1 X2
         have r₂ := f163801_22
         grind)
      | exact resolve f163801_12 f163801_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f163801_25 : ∀ X0 X1 X2 : G, (τ (k (M.op X2 X2) (M.op X1 X1))) = (M.op (M.op (σ x) X0) (τ X1)) := by
      intro X0 X1 X2
      first
      | (have i₁ := f163801_24 X0 X1 X2
         have i₂ := f163801_23 X0
         grind)
      | exact superpose f163801_23 f163801_24
      | exact resolve f163801_24 f163801_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f163801_29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f163801_14 X2 X0 X3
         have i₂ := f163801_14 X2 X0 X1
         grind)
      | (have i₁ := f163801_14 X2 X0 X2
         have i₂ := f163801_14 X0 X2 X2
         grind)
      | exact superpose f163801_14 f163801_14
      | exact resolve f163801_14 f163801_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f163801_91 : ∀ X0 : G, (M.op (M.op (σ x) X0) (τ X1)) ≠ (M.op (M.op (σ x) X0) (τ X1)) := by
      intro X0
      first
      | (have i₁ := f163801_21
         have i₂ := f163801_25 X0 X1 X2
         grind)
      | exact superpose f163801_25 f163801_21
      | (have r₁ := f163801_21
         have r₂ := f163801_25 X0 X1 X2
         grind)
      | exact resolve f163801_21 f163801_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f163801_99 : False := by
      first
      | (have r₁ := f163801_91 x
         have r₂ := f163801_29 (σ x) X0 (τ X1) x
         grind)
      | (have r₁ := f163801_91 x
         have r₂ := f163801_29 (σ x) x (τ X1) X0
         grind)
      | exact resolve f163801_91 f163801_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f163801_99
  clear eq36243 eq163751
  have eq163854 : ∀ X1 X2 : G, (τ (k (M.op X2 X2) (M.op X1 X1))) = (M.op (σ x) (τ X1)) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | exact superpose eq36245 eq163801
    | exact resolve eq163801 eq36245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163801
  have eq163886 : ∀ X1 : G, (τ (M.op (σ x) X1)) = (M.op (σ x) (τ X1)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq36833 eq163854
    | exact resolve eq163854 eq36833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36833 eq163854
  have eq163897 : (τ (σ x)) = (M.op (σ x) (τ (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq163886 (σ y)
       have i₂ := eq36140
       grind)
    | exact superpose eq36140 eq163886
    | exact resolve eq163886 eq36140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36140 eq163886
  have eq163997 : (τ (σ x)) = (M.op (σ x) (τ (σ y))) ∨ x = (M.op x y) := by grind
  clear eq163897
  have eq164043 : (τ (σ x)) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq163997
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq163997
    | exact resolve eq163997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163997
  have eq164082 : x = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq164043
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq164043
    | exact resolve eq164043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164043
  have eq164125 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq36245 X0 y
       have i₂ := eq164082
       grind)
    | exact superpose eq164082 eq36245
    | exact resolve eq36245 eq164082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36245
  have eq164286 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq164125 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164125
  have eq164536 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq164286 y
       have i₂ := eq164082
       grind)
    | exact superpose eq164082 eq164286
    | exact resolve eq164286 eq164082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164082 eq164286
  have eq164888 : x = (M.op x y) := by grind
  clear eq164536
  have eq164980 : x = (M.op x y) := by grind
  clear eq164888
  have eq165021 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq164980
       grind)
    | exact superpose eq164980 eq16
    | exact resolve eq16 eq164980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165023 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 x y X0 X1
       have i₂ := eq164980
       grind)
    | exact superpose eq164980 eq62
    | exact resolve eq62 eq164980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq165025 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq71 x y X0 X1
       have i₂ := eq164980
       grind)
    | exact superpose eq164980 eq71
    | exact resolve eq71 eq164980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq165029 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) x) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq148 X0 x y
       have i₂ := eq164980
       grind)
    | exact superpose eq164980 eq148
    | exact resolve eq148 eq164980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq165277 : ∀ X0 X2 X3 X4 X5 : G, (k (M.op X3 X4) (M.op X2 X5)) = (M.op (M.op x X0) X2) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq37472 x x X0 X2 X3 X4 X5
       have i₂ := eq165023 X0 x
       grind)
    | exact superpose eq165023 eq37472
    | exact resolve eq37472 eq165023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37472
  have eq165772 : ∀ X2 X3 X4 X5 : G, (k (M.op X3 X4) (M.op X2 X5)) = (M.op x X2) := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq165277 x X2 X3 X4 X5
       have i₂ := eq165023 X2 x
       grind)
    | exact superpose eq165023 eq165277
    | exact resolve eq165277 eq165023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165277
  have eq165941 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq165025 (M.op X0 X1) x
       have i₂ := eq165025 X0 X1
       grind)
    | exact superpose eq165025 eq165025
    | exact resolve eq165025 eq165025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166150 : ∀ X0 X2 : G, (M.op x x) ≠ (M.op (M.op x X0) x) ∨ (M.op (M.op x x) X2) = (k X2 (M.op x x)) := by
    intro X0 X2
    first
    | (have i₁ := eq39337 X0 x x X2
       have i₂ := eq165025 X0 x
       grind)
    | exact superpose eq165025 eq39337
    | (have j0 := eq39337 X0 x x X2
       grind)
    | exact resolve eq39337 eq165025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39337
  have eq166439 : ∀ X2 : G, (M.op (M.op x x) X2) = (k X2 (M.op x x)) := by
    intro X2
    first
    | (have j0 := eq166150 x X2
       grind)
    | (have r₁ := eq166150 x X2
       have r₂ := eq165023 x x
       grind)
    | exact resolve eq166150 eq165023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166150
  have eq166582 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq165941 X0 X1
       have i₂ := eq165025 x X0
       grind)
    | exact superpose eq165025 eq165941
    | exact resolve eq165941 eq165025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165025 eq165941
  have eq166629 : ∀ X2 : G, (M.op x X2) = (k X2 (M.op x x)) := by
    intro X2
    first
    | (have i₁ := eq166439 X2
       have i₂ := eq165023 X2 x
       grind)
    | exact superpose eq165023 eq166439
    | exact resolve eq166439 eq165023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166439
  have eq166789 : ∀ X0 : G, (M.op x x) = (M.op x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq166582 (τ X0) (τ X0)
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq166582
    | exact resolve eq166582 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq168543 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) X4) = (M.op (M.op x (σ X0)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5352 X0 X1 X2 X3 X4 x
       have i₂ := eq165029 X0
       grind)
    | exact superpose eq165029 eq5352
    | exact resolve eq5352 eq165029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5352
  have eq168544 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X3 X4)) = (M.op (M.op x (σ X0)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5699 X0 X1 X2 X3 X4 x
       have i₂ := eq165029 X0
       grind)
    | exact superpose eq165029 eq5699
    | exact resolve eq5699 eq165029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5699 eq165029
  have eq168783 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X3 X4)) = (M.op x X1) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq168544 x X1 X2 X3 X4
       have i₂ := eq165023 X1 (σ x)
       grind)
    | exact superpose eq165023 eq168544
    | exact resolve eq168544 eq165023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168544
  have eq168784 : ∀ X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) X4) = (M.op x X4) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq168543 x X1 X2 X3 X4
       have i₂ := eq165023 X4 (σ x)
       grind)
    | exact superpose eq165023 eq168543
    | exact resolve eq168543 eq165023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168543
  have eq178425 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op X0 X1) X2) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq168784 X0 X1 X2 y
       have i₂ := eq164980
       grind)
    | exact superpose eq164980 eq168784
    | exact resolve eq168784 eq164980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168784
  have eq179751 : ∀ X0 X1 : G, x = (M.op (M.op (σ (M.op X0 X0)) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq178425 (σ X0) (σ X0) X1
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq178425
    | exact resolve eq178425 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178425
  have eq180269 : ∀ X0 X2 : G, x = (M.op (M.op (σ (M.op x X0)) X2) y) := by
    intro X0 X2
    first
    | (have i₁ := eq179751 (M.op X0 x) X2
       have i₂ := eq168783 X0 x X0 x
       grind)
    | exact superpose eq168783 eq179751
    | exact resolve eq179751 eq168783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179751
  have eq184591 : ∀ X0 : G, x = (M.op (σ (M.op (M.op x X0) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq150 (M.op x X0) x y
       have i₂ := eq180269 X0 x
       grind)
    | exact superpose eq180269 eq150
    | exact resolve eq150 eq180269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq180269
  have eq184864 : x = (M.op (σ (M.op x x)) y) := by
    first
    | (have i₁ := eq184591 x
       have i₂ := eq168783 x x x x
       grind)
    | exact superpose eq168783 eq184591
    | exact resolve eq184591 eq168783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168783 eq184591
  have eq185363 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) (M.op (σ (M.op x x)) (σ (M.op x x)))) = (M.op x (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29895 (σ (M.op x x)) y X0 X1
       have i₂ := eq184864
       grind)
    | exact superpose eq184864 eq29895
    | exact resolve eq29895 eq184864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29895 eq184864
  have eq185425 : ∀ X1 : G, (M.op x x) = (k (σ (M.op X1 X1)) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
    intro X1
    first
    | (have i₁ := eq185363 x X1
       have i₂ := eq166789 x
       grind)
    | exact superpose eq166789 eq185363
    | exact resolve eq185363 eq166789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166789 eq185363
  have eq185490 : ∀ X1 : G, (M.op x x) = (k (σ (M.op X1 X1)) (σ (M.op (M.op x x) (M.op x x)))) := by
    intro X1
    first
    | (have i₁ := eq185425 X1
       have i₂ := eq137 (M.op x x)
       grind)
    | exact superpose eq137 eq185425
    | exact resolve eq185425 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq185425
  have eq185509 : ∀ X1 : G, (M.op x x) = (σ (k (M.op X1 X1) (M.op (M.op x x) (M.op x x)))) := by
    intro X1
    first
    | (have i₁ := eq185490 X1
       have i₂ := eq15 (M.op X1 X1) (M.op (M.op x x) (M.op x x))
       grind)
    | exact superpose eq15 eq185490
    | exact resolve eq185490 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185490
  have eq185512 : (M.op x x) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq185509 x
       have i₂ := eq165772 (M.op x x) x x (M.op x x)
       grind)
    | exact superpose eq165772 eq185509
    | exact resolve eq185509 eq165772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165772 eq185509
  have eq185515 : (M.op x x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq185512
       have i₂ := eq166582 x x
       grind)
    | exact superpose eq166582 eq185512
    | exact resolve eq185512 eq166582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166582 eq185512
  have eq187861 : ∀ X0 : G, (σ (k X0 (M.op x x))) = (k (σ X0) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op x x)
       have i₂ := eq185515
       grind)
    | exact superpose eq185515 eq15
    | exact resolve eq15 eq185515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185515
  have eq187924 : ∀ X0 : G, (σ (k X0 (M.op x x))) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq187861 X0
       have i₂ := eq166629 (σ X0)
       grind)
    | exact superpose eq166629 eq187861
    | exact resolve eq187861 eq166629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187861
  have eq187982 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq187924 X0
       have i₂ := eq166629 X0
       grind)
    | exact superpose eq166629 eq187924
    | exact resolve eq187924 eq166629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166629 eq187924
  have eq190770 : (σ x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq187982 y
       have i₂ := eq164980
       grind)
    | exact superpose eq164980 eq187982
    | exact resolve eq187982 eq164980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164980 eq187982
  have eq191032 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq165023 X0 (σ y)
       have i₂ := eq190770
       grind)
    | exact superpose eq190770 eq165023
    | exact resolve eq165023 eq190770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165023
  have eq191273 : (σ x) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq165021
       have i₂ := eq191032 (σ y)
       grind)
    | exact superpose eq191032 eq165021
    | exact resolve eq165021 eq191032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165021 eq191032
  have eq191797 : False := by grind
  exact eq191797

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_y_pyx_pxy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X0 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X2 X0 X2
       have i₂ := eq14 X0 X2 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X3) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X2 X2) (M.op X2 X2)) ∨ (M.op (M.op X0 X1) X2) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X1 X2) (M.op X1 X2)) ∨ (M.op (M.op X0 X0) X1) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq72 (σ X0)
       grind)
    | exact superpose eq72 eq10
    | exact resolve eq10 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq72 x
       grind)
    | exact superpose eq72 eq43
    | exact resolve eq43 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq72 sF2
       grind)
    | exact superpose eq72 eq49
    | exact resolve eq49 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq72 x
       grind)
    | exact superpose eq72 eq76
    | exact resolve eq76 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq72 sF2
       grind)
    | exact superpose eq72 eq75
    | exact resolve eq75 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq74
    | exact resolve eq74 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq106 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq107 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24 eq36
  have eq111 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq72 sF3
       grind)
    | exact superpose eq72 eq107
    | exact resolve eq107 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq113 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq72 y
       grind)
    | exact superpose eq72 eq111
    | exact resolve eq111 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq83 y x
       grind)
    | exact superpose eq83 eq106
    | (have j1 := eq83 x x
       grind)
    | exact resolve eq106 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq150 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq153 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq150
       have i₂ := eq72 sF1
       grind)
    | exact superpose eq72 eq150
    | exact resolve eq150 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq155 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq153
       have i₂ := eq72 sF0
       grind)
    | exact superpose eq72 eq153
    | exact resolve eq153 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq242 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq53 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) x
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0
       have i₂ := eq14 X0 sF2 x
       grind)
    | (have i₁ := eq54 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 (τ X1)) X2
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq410 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq54 eq242
    | exact resolve eq242 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op x X0)
       have i₂ := eq242 X0 (M.op x X0)
       grind)
    | (have i₁ := eq53 (M.op x y)
       have i₂ := eq242 X0 (M.op x y)
       grind)
    | exact superpose eq242 eq53
    | exact resolve eq53 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq415 X0
       have i₂ := eq14 x sF0 (M.op x X0)
       grind)
    | exact superpose eq14 eq415
    | exact resolve eq415 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq427 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq424 X0
       have i₂ := eq242 x sF0
       grind)
    | exact superpose eq242 eq424
    | exact resolve eq424 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq456 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X0 X0) x X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X0 x X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq54
  have eq533 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq467 (M.op X0 X1) x
       have i₂ := eq467 X0 X1
       grind)
    | (have i₁ := eq467 (M.op x y) X0
       have i₂ := eq467 X0 X1
       grind)
    | exact superpose eq467 eq467
    | exact resolve eq467 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 sF0 X1
       have i₂ := eq14 sF0 x x
       grind)
    | (have i₁ := eq533 x X1
       have i₂ := eq14 x sF0 x
       grind)
    | exact superpose eq14 eq533
    | exact resolve eq533 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq566 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq556 X0 X1
       have i₂ := eq242 x sF0
       grind)
    | exact superpose eq242 eq556
    | exact resolve eq556 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq585 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq468 (M.op X0 X1) x
       have i₂ := eq467 X0 X1
       grind)
    | (have i₁ := eq468 (M.op x y) X0
       have i₂ := eq467 X0 X1
       grind)
    | exact superpose eq467 eq468
    | exact resolve eq468 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) (σ x)) := by
    first
    | exact superpose eq410 eq468
    | exact resolve eq468 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq468 eq592
    | exact resolve eq592 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq613 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq468 eq585
    | exact resolve eq585 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq804 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X1 X1) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 x X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1372 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op X0 X0) (σ x)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq70
    | (have j0 := eq70 X0 (σ x) (σ y)
       grind)
    | exact resolve eq70 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1386 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (M.op (M.op X0 X0) (σ x)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq608 eq1372
    | (have j0 := eq1372 X0
       grind)
    | exact resolve eq1372 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq1372
  have eq1396 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (M.op (M.op X0 X0) (σ x)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq468 eq1386
    | (have j0 := eq1386 X0
       grind)
    | (have r₁ := eq1386 (M.op x y)
       have r₂ := eq468 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1386 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1403 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq468 eq1396
    | (have j0 := eq1396 X0
       grind)
    | exact resolve eq1396 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1613 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq79 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq79
    | exact resolve eq79 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1660 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq1613
       have i₂ := eq72 x
       grind)
    | exact superpose eq72 eq1613
    | exact resolve eq1613 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613
  have eq1663 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq1660
       have i₂ := eq242 x (M.op x x)
       grind)
    | exact superpose eq242 eq1660
    | exact resolve eq1660 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1665 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq427 eq1663
    | exact resolve eq1663 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1663
  have eq1667 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1665
       have i₂ := eq72 sF2
       grind)
    | exact superpose eq72 eq1665
    | exact resolve eq1665 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1665
  have eq1669 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq249 eq1667
    | exact resolve eq1667 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq1667
  have eq1671 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq613 eq1669
    | exact resolve eq1669 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq1672 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq155 eq1671
    | exact resolve eq1671 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671
  have eq2259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq122 eq83
    | (have j0 := eq83 x (σ x)
       grind)
    | exact resolve eq83 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq122
  have eq2260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq2259
    | exact resolve eq2259 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2263 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2260
       have r₂ := eq27
       grind)
    | exact resolve eq2260 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2266 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2263 eq77
    | exact resolve eq77 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2263
  have eq2317 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq2266
    | exact resolve eq2266 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq2318 : x = (M.op x x) := by grind
  clear eq2317
  have eq2332 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq78
    | exact resolve eq78 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2337 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq242 x X0
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq242
    | exact resolve eq242 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2360 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq467 x x
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq467
    | exact resolve eq467 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2370 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2360
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq2360
    | exact resolve eq2360 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2392 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2332
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2332
    | exact resolve eq2332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2332
  have eq2417 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2370 eq566
    | exact resolve eq566 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2422 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2370 eq2417
    | exact resolve eq2417 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417
  have eq2455 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2392 eq468
    | exact resolve eq468 eq2392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2463 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2392 eq2455
    | exact resolve eq2455 eq2392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq2498 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2422 eq155
    | exact resolve eq155 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq2543 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2498
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2498
    | exact resolve eq2498 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2498
  have eq2563 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq2463 eq566
    | exact resolve eq566 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq2463
  have eq2569 : x = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq2422 eq2563
    | exact resolve eq2563 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563
  have eq2671 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq2569 eq613
    | exact resolve eq613 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq2676 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) x) := by
    first
    | exact superpose eq1672 eq2671
    | exact resolve eq2671 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq2683 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq410 eq2676
    | exact resolve eq2676 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq2676
  have eq2685 : x = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2569 eq2683
    | exact resolve eq2683 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2686 : x = (σ x) := by
    first
    | exact superpose eq2543 eq2685
    | exact resolve eq2685 eq2543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq2688 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq2686 eq26
    | exact resolve eq26 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2689 : x = (τ x) := by
    first
    | exact superpose eq2686 eq28
    | exact resolve eq28 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2790 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op x y) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq2392 eq246
    | exact resolve eq246 eq2392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392
  have eq2883 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq2569 eq2790
    | exact resolve eq2790 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569 eq2790
  have eq2919 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq468 eq2883
    | exact resolve eq2883 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq2883
  have eq3488 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq2337 eq53
    | exact resolve eq53 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3539 : (M.op x (M.op x y)) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq3488
       have i₂ := eq14 x x sF0
       grind)
    | exact superpose eq14 eq3488
    | exact resolve eq3488 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488
  have eq3575 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3539
       have i₂ := eq467 x x
       grind)
    | exact superpose eq467 eq3539
    | exact resolve eq3539 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq3539
  have eq3594 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq2370 eq3575
    | exact resolve eq3575 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370 eq3575
  have eq3803 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op (M.op X1 X1) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2337 eq804
    | exact resolve eq804 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq3804 : ∀ X1 X2 : G, (M.op (M.op x y) X1) = (M.op (M.op X1 X1) (M.op x X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq3803 x X1 X2
       have i₂ := eq242 x X1
       grind)
    | (have i₁ := eq3803 y X1 X2
       have i₂ := eq242 x X1
       grind)
    | exact superpose eq242 eq3803
    | (have j0 := eq3803 y X1 X2
       grind)
    | exact resolve eq3803 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3803
  have eq3805 : ∀ X1 X2 : G, (M.op x X1) = (M.op (M.op X1 X1) (M.op x X2)) := by
    intro X1 X2
    first
    | exact superpose eq2337 eq3804
    | exact resolve eq3804 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3804
  have eq3938 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3805 (M.op x X0) X1
       have i₂ := eq242 X0 (M.op x X0)
       grind)
    | (have i₁ := eq3805 (M.op x y) x
       have i₂ := eq242 X0 (M.op x y)
       grind)
    | exact superpose eq242 eq3805
    | exact resolve eq3805 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4010 : ∀ X0 X1 X2 : G, (M.op (M.op x x) (M.op X0 X1)) = (M.op (M.op (M.op X2 X2) X0) (M.op x x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 X0 (M.op x x) X1
       have i₂ := eq3805 x x
       grind)
    | exact superpose eq3805 eq56
    | exact resolve eq56 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq4056 : ∀ X0 X1 X2 : G, (M.op (M.op x x) (M.op X0 X1)) = (M.op (M.op (M.op x y) X2) (M.op x x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4010 X0 X1 X2
       have i₂ := eq456 X2 (M.op x x) X0
       grind)
    | exact superpose eq456 eq4010
    | exact resolve eq4010 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq4010
  have eq4115 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq427 eq3938
    | exact resolve eq3938 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq3938
  have eq4139 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (M.op (M.op (M.op x y) X2) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4056 X0 X1 X2
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq4056
    | exact resolve eq4056 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318 eq4056
  have eq4192 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq4115 X0 x
       have i₂ := eq3805 sF0 x
       grind)
    | exact superpose eq3805 eq4115
    | exact resolve eq4115 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805 eq4115
  have eq4213 : ∀ X0 X1 : G, (M.op (M.op x x) (M.op x y)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4139 X0 X1 sF0
       have i₂ := eq14 sF0 x x
       grind)
    | (have i₁ := eq4139 X0 X1 x
       have i₂ := eq14 x sF0 x
       grind)
    | exact superpose eq14 eq4139
    | exact resolve eq4139 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq4254 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq3594 eq4192
    | exact resolve eq4192 eq3594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594 eq4192
  have eq4272 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4213 X0 X1
       have i₂ := eq242 x sF0
       grind)
    | exact superpose eq242 eq4213
    | exact resolve eq4213 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213
  have eq4312 : ∀ X0 X1 : G, x = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq2422 eq4272
    | exact resolve eq4272 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422 eq4272
  have eq4403 : ∀ X1 : G, (M.op x X1) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op x X1) = (k x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq69 x (M.op x x) x
       have i₂ := eq4254 x
       grind)
    | exact superpose eq4254 eq69
    | exact resolve eq69 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq4254
  have eq4421 : ∀ X1 : G, (M.op x X1) ≠ (M.op (M.op (M.op x y) X1) X1) ∨ (M.op x X1) = (k x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq4403 X1
       have i₂ := eq246 X1 X1
       grind)
    | exact superpose eq246 eq4403
    | (have j0 := eq4403 X1
       grind)
    | exact resolve eq4403 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq4403
  have eq4438 : ∀ X1 : G, (M.op x X1) ≠ (M.op (M.op x X1) X1) ∨ (M.op x X1) = (k x (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq2337 eq4421
    | (have j0 := eq4421 X1
       grind)
    | exact resolve eq4421 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4421
  have eq4446 : ∀ X1 : G, (M.op (M.op x y) X1) ≠ (M.op x X1) ∨ (M.op x X1) = (k x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq4438 X1
       have i₂ := eq242 X1 X1
       grind)
    | (have i₁ := eq4438 y
       have i₂ := eq242 x y
       grind)
    | exact superpose eq242 eq4438
    | (have j0 := eq4438 X1
       grind)
    | exact resolve eq4438 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq4438
  have eq4451 : ∀ X1 : G, (M.op x X1) = (k x (M.op X1 X1)) := by
    intro X1
    first
    | (have j0 := eq4446 X1
       grind)
    | (have r₁ := eq4446 x
       have r₂ := eq2337 x
       grind)
    | exact resolve eq4446 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337 eq4446
  have eq4478 : ∀ X0 : G, x = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4312 (σ X0) (σ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq4312
    | exact resolve eq4312 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq4312
  have eq6773 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2919 eq1403
    | (have j0 := eq1403 X0
       grind)
    | exact resolve eq1403 eq2919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq6774 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1672 eq6773
    | (have j0 := eq6773 X0
       grind)
    | exact resolve eq6773 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672 eq6773
  have eq6775 : ∀ X0 : G, (σ x) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2543 eq6774
    | (have j0 := eq6774 X0
       grind)
    | exact resolve eq6774 eq2543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543 eq6774
  have eq6776 : ∀ X0 : G, (σ x) ≠ (M.op x X0) ∨ (M.op x X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2919 eq6775
    | (have j0 := eq6775 X0
       grind)
    | exact resolve eq6775 eq2919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919 eq6775
  have eq6777 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2686 eq6776
    | (have j0 := eq6776 X0
       grind)
    | exact resolve eq6776 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686 eq6776
  have eq6783 : ∀ X0 : G, x ≠ x ∨ x = (k (σ (M.op X0 X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq6777 (σ (M.op X0 X0))
       have i₂ := eq4478 X0
       grind)
    | exact superpose eq4478 eq6777
    | (have r₁ := eq6777 (σ (M.op X0 X0))
       have r₂ := eq4478 X0
       grind)
    | exact resolve eq6777 eq4478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478 eq6777
  have eq6798 : ∀ X0 : G, x = (k (σ (M.op X0 X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq6783 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6783
  have eq6892 : ∀ X0 : G, (τ x) = (k (M.op X0 X0) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq6798 eq395
    | exact resolve eq395 eq6798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq6895 : ∀ X0 : G, x = (k (M.op X0 X0) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq6892 X0
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq6892
    | exact resolve eq6892 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689 eq6892
  have eq7707 : ∀ X0 X1 : G, (k x (σ X1)) = (σ (k (k (M.op X0 X0) (τ (M.op (σ x) (σ y)))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6798 eq393
    | exact resolve eq393 eq6798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq6798
  have eq7769 : ∀ X1 : G, (k x (σ X1)) = (σ (k x X1)) := by
    intro X1
    first
    | exact superpose eq6895 eq7707
    | exact resolve eq7707 eq6895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6895 eq7707
  have eq10034 : (σ (k x (M.op y y))) = (k x (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq7769 (M.op y y)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq7769
    | exact resolve eq7769 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq7769
  have eq10087 : (σ (k x (M.op y y))) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq10034
       have i₂ := eq4451 sF3
       grind)
    | exact superpose eq4451 eq10034
    | exact resolve eq10034 eq4451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10034
  have eq10097 : (M.op (σ x) (σ y)) = (σ (k x (M.op y y))) := by
    first
    | exact superpose eq2688 eq10087
    | exact resolve eq10087 eq2688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688 eq10087
  have eq10107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10097
       have i₂ := eq4451 y
       grind)
    | exact superpose eq4451 eq10097
    | exact resolve eq10097 eq4451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4451 eq10097
  have eq10114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10107
    | exact resolve eq10107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10107
  have eq10121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10114
    | exact resolve eq10114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10114
  have eq10127 : False := by grind
  exact eq10127
