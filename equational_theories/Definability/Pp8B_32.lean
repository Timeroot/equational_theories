import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq78 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq96
    | (have j0 := eq96 (σ X0) (σ X1)
       grind)
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq96 y x
       grind)
    | exact superpose eq96 eq75
    | (have j1 := eq96 y x
       grind)
    | exact resolve eq75 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ y) (σ x)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
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
  have eq248 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq311 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq362 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq96 X1 (τ X0)
       grind)
    | exact superpose eq96 eq38
    | (have j1 := eq96 X1 (τ X0)
       grind)
    | exact resolve eq38 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq96
  have eq515 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X2) (M.op X0 X1)) ∨ (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X1) = (k X1 (M.op (M.op X0 X2) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 X2) (M.op X0 X1))
       have i₂ := eq53 X1 X0 X2
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 (M.op X0 X2) (M.op X0 X1)
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq770 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq79
    | (have r₁ := eq79
       have r₂ := eq131
       grind)
    | exact resolve eq79 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq131
  have eq771 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq770
  have eq840 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X0 X2) X5) (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0) X5
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq56
  have eq1063 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq100 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq17106 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq771 eq122
    | exact resolve eq122 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq17112 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq17106
  have eq17116 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17112
       have r₂ := eq133
       grind)
    | exact resolve eq17112 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq17112
  have eq17133 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17116 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17116
       grind)
    | exact resolve eq13 eq17116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17116
  have eq17182 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17133
  have eq17194 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17182
    | exact resolve eq17182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17182
  have eq17200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17194 eq122
    | exact resolve eq122 eq17194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq17194
  have eq17204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17200
  have eq17208 : x = (M.op x y) := by
    first
    | (have r₁ := eq17204
       have r₂ := eq27
       grind)
    | exact resolve eq17204 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17204
  have eq17210 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17208 eq20
    | exact resolve eq20 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq17216 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | exact superpose eq17208 eq78
    | (have r₁ := eq78
       have r₂ := eq17208
       grind)
    | exact resolve eq78 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq17220 : y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq17208 eq222
    | exact resolve eq222 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq17242 : x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq17216
  have eq17247 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq17220
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17220
    | exact resolve eq17220 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17220
  have eq17253 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17210
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17210
    | exact resolve eq17210 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17210
  have eq17254 : y = (M.op x x) := by
    first
    | exact superpose eq17208 eq17247
    | exact resolve eq17247 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17247
  have eq18300 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq17254
       grind)
    | exact superpose eq17254 eq50
    | exact resolve eq50 eq17254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18391 : x = (M.op (M.op x x) y) := by
    first
    | exact superpose eq17208 eq18300
    | exact resolve eq18300 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18300
  have eq18398 : x = (M.op y y) := by
    first
    | (have i₁ := eq18391
       have i₂ := eq17254
       grind)
    | exact superpose eq17254 eq18391
    | exact resolve eq18391 eq17254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18391
  have eq20203 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq248 sF0 (M.op (M.op x x) sF0)
       have i₂ := eq840 x x sF0 y
       grind)
    | exact superpose eq840 eq248
    | exact resolve eq248 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq840
  have eq20295 : ∀ X0 : G, x = (M.op (M.op (M.op X0 x) x) y) := by
    intro X0
    first
    | exact superpose eq17208 eq20203
    | exact resolve eq20203 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20203
  have eq21106 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq574 x X0 x y
       have i₂ := eq20295 X0
       grind)
    | exact superpose eq20295 eq574
    | exact resolve eq574 eq20295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq20295
  have eq21169 : ∀ X0 : G, x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq21106 X0
       have i₂ := eq17254
       grind)
    | exact superpose eq17254 eq21106
    | exact resolve eq21106 eq17254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17254 eq21106
  have eq21223 : ∀ X0 : G, y = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq21169 X0
       grind)
    | exact superpose eq21169 eq14
    | exact resolve eq14 eq21169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21361 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x y) (M.op X0 y)) y) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 y)
       have i₂ := eq21223 X0
       grind)
    | exact superpose eq21223 eq50
    | exact resolve eq50 eq21223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq21451 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x (M.op X0 y)) y) := by
    intro X0
    first
    | exact superpose eq17208 eq21361
    | exact resolve eq21361 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21361
  have eq21465 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq21451 X0
       have i₂ := eq21223 X0
       grind)
    | exact superpose eq21223 eq21451
    | exact resolve eq21451 eq21223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21223 eq21451
  have eq21467 : ∀ X0 : G, x = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq21465 X0
       have i₂ := eq18398
       grind)
    | exact superpose eq18398 eq21465
    | exact resolve eq21465 eq18398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18398 eq21465
  have eq21623 : ∀ X0 : G, (σ x) = (k (σ y) X0) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq362 X0 y
       have i₂ := eq21467 (τ X0)
       grind)
    | exact superpose eq21467 eq362
    | exact resolve eq362 eq21467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq21467
  have eq21743 : ∀ X0 : G, (σ x) = (k (σ y) X0) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq21623 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21623
    | (have j0 := eq21623 X0
       grind)
    | exact resolve eq21623 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21623
  have eq21793 : ∀ X0 : G, (σ x) = (k (σ y) X0) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq21743 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21743
    | (have j0 := eq21743 X0
       grind)
    | exact resolve eq21743 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21743
  have eq21809 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) X0) ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq17253 eq21793
    | (have j0 := eq21793 X0
       grind)
    | exact resolve eq21793 eq17253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21793
  have eq40156 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (τ (σ y)) X0) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | exact superpose eq21809 eq311
    | (have j1 := eq21809 (σ X0)
       grind)
    | exact resolve eq311 eq21809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq21809
  have eq40175 : ∀ X0 : G, (τ (σ (M.op x y))) = (k y X0) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | exact superpose eq29 eq40156
    | (have j0 := eq40156 X0
       grind)
    | exact resolve eq40156 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40156
  have eq40183 : ∀ X0 : G, (M.op x y) = (k y X0) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | exact superpose eq30 eq40175
    | (have j0 := eq40175 X0
       grind)
    | exact resolve eq40175 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq40175
  have eq40189 : ∀ X0 : G, x = (k y X0) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | exact superpose eq17208 eq40183
    | (have j0 := eq40183 X0
       grind)
    | exact resolve eq40183 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40183
  have eq40194 : ∀ X0 : G, x = (k y X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq40189 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq40189
    | (have j0 := eq40189 X0
       grind)
    | exact resolve eq40189 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40189
  have eq53760 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x X0) (M.op x y)) ∨ (M.op (M.op (M.op x X0) (M.op x y)) y) = (k y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq605 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq605
    | (have j0 := eq605 x y X0
       grind)
    | exact resolve eq605 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq605
  have eq53925 : ∀ X0 : G, x ≠ (M.op (M.op x X0) x) ∨ (M.op (M.op (M.op x X0) (M.op x y)) y) = (k y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq17208 eq53760
    | (have j0 := eq53760 X0
       grind)
    | exact resolve eq53760 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53760
  have eq54040 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) y) = (k y (M.op (M.op x X0) x)) ∨ x ≠ (M.op (M.op x X0) x) := by
    intro X0
    first
    | exact superpose eq17208 eq53925
    | (have j0 := eq53925 X0
       grind)
    | exact resolve eq53925 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17208 eq53925
  have eq54119 : ∀ X0 : G, x = (k y (M.op (M.op x X0) x)) ∨ x ≠ (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq54040 X0
       have i₂ := eq21169 (M.op x X0)
       grind)
    | exact superpose eq21169 eq54040
    | (have j0 := eq54040 X0
       grind)
    | exact resolve eq54040 eq21169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21169 eq54040
  have eq54144 : ∀ X0 : G, x = (k y (M.op (M.op x X0) x)) := by
    intro X0
    first
    | (have j0 := eq54119 X0
       have j1 := eq40194 (M.op (M.op x X0) x)
       grind)
    | (have r₁ := eq54119 X0
       have r₂ := eq40194 (M.op (M.op x X0) x)
       grind)
    | exact resolve eq54119 eq40194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40194 eq54119
  have eq54185 : ∀ X0 : G, x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq54144 (M.op X0 x)
       have i₂ := eq515 x X0
       grind)
    | exact superpose eq515 eq54144
    | exact resolve eq54144 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515 eq54144
  have eq58220 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1063 x y
       have i₂ := eq17242
       grind)
    | exact superpose eq17242 eq1063
    | (have j0 := eq1063 x y
       grind)
    | exact resolve eq1063 eq17242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17242
  have eq58222 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq58220
  have eq58228 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq58222
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58222
    | exact resolve eq58222 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58222
  have eq58238 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq58228
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq58228
    | exact resolve eq58228 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58228
  have eq58248 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq58238
    | exact resolve eq58238 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58238
  have eq58258 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17253 eq58248
    | exact resolve eq58248 eq17253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58248
  have eq58267 : x = (M.op y x) := by
    first
    | (have r₁ := eq58258
       have r₂ := eq27
       grind)
    | exact resolve eq58258 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58258
  have eq58320 : x = (k y x) := by
    first
    | (have i₁ := eq54185 y
       have i₂ := eq58267
       grind)
    | exact superpose eq58267 eq54185
    | exact resolve eq54185 eq58267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54185 eq58267
  have eq58521 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1063 x y
       have i₂ := eq58320
       grind)
    | exact superpose eq58320 eq1063
    | (have j0 := eq1063 x y
       grind)
    | exact resolve eq1063 eq58320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063 eq58320
  have eq58523 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq58521
  have eq58529 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq58523
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58523
    | exact resolve eq58523 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq58523
  have eq58539 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq58529
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq58529
    | exact resolve eq58529 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq58529
  have eq58549 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq58539
    | exact resolve eq58539 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq58539
  have eq58559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17253 eq58549
    | exact resolve eq58549 eq17253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17253 eq58549
  have eq58568 : False := by grind
  exact eq58568

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyy_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X1) (M.op X0 X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X1) (M.op X0 X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq101 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq101 X0 X0 X2
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq101 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq101 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq185 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq299 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq185 X1 X0
       grind)
    | exact superpose eq185 eq9
    | exact resolve eq9 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq330 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X0
       have i₂ := eq299 X1 X0
       grind)
    | exact superpose eq299 eq9
    | exact resolve eq9 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq1125 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X1 (M.op (M.op X0 x) X0)
       have i₂ := eq116 X1 X0 x
       grind)
    | exact superpose eq116 eq330
    | (have j1 := eq116 X1 X0 x
       grind)
    | exact resolve eq330 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq330
  have eq1166 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1125 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1125 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq1125 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq1125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1281 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1166 (σ X1) (σ X0)
       grind)
    | exact superpose eq1166 eq15
    | exact resolve eq15 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1281 X0 X1
       have i₂ := eq1166 X1 X0
       grind)
    | exact superpose eq1166 eq1281
    | exact resolve eq1281 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166 eq1281
  have eq1603 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1288 x y
       grind)
    | exact superpose eq1288 eq16
    | (have r₁ := eq16
       have r₂ := eq1288 x y
       grind)
    | exact resolve eq16 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1651 : False := by grind
  exact eq1651

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_y_pxy_x_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq43
    | exact resolve eq43 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq49
    | exact resolve eq49 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq72
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq72
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq70
    | exact resolve eq70 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq97 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq98 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq100 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq102 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq68 sF3
       grind)
    | exact superpose eq68 eq98
    | exact resolve eq98 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq68 y
       grind)
    | exact superpose eq68 eq102
    | exact resolve eq102 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq97
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq130 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq133 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq130
       have i₂ := eq68 sF1
       grind)
    | exact superpose eq68 eq130
    | exact resolve eq130 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq135 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq133
       have i₂ := eq68 sF0
       grind)
    | exact superpose eq68 eq133
    | exact resolve eq133 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq133
  have eq233 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
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
  have eq234 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) y)) := by
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
  have eq535 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq254 eq53
    | exact resolve eq53 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq590 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq258 eq53
    | exact resolve eq53 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq594 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op (M.op (M.op x y) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq596 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq600 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq603 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq731 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1491 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | (have i₁ := eq512 (M.op x X0) (M.op (M.op (M.op x x) x) X0)
       have i₂ := eq52 x x x X0
       grind)
    | exact superpose eq52 eq512
    | exact resolve eq512 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq512
  have eq1833 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq535
    | exact resolve eq535 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq2064 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq544 X1 X0
       grind)
    | exact superpose eq544 eq14
    | exact resolve eq14 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2623 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq594 (M.op sF0 X0) X0
       have i₂ := eq14 X0 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq14 eq594
    | exact resolve eq594 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq2839 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq596 (M.op sF4 X0) X0
       have i₂ := eq14 X0 sF4 (M.op sF4 X0)
       grind)
    | exact superpose eq14 eq596
    | exact resolve eq596 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq3003 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq586 eq600
    | exact resolve eq600 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq600
  have eq3032 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq3003 X0
       have i₂ := eq544 y (M.op x X0)
       grind)
    | exact superpose eq544 eq3003
    | exact resolve eq3003 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq3129 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq590 eq603
    | exact resolve eq603 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq603
  have eq3156 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3129 X0
       have i₂ := eq544 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq544 eq3129
    | exact resolve eq3129 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq3129
  have eq5961 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq234 eq2623
    | exact resolve eq2623 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq2623
  have eq6023 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq5961
       have i₂ := eq2064 x x
       grind)
    | exact superpose eq2064 eq5961
    | exact resolve eq5961 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5961
  have eq6327 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq3032 eq572
    | exact resolve eq572 eq3032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3032
  have eq6332 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq3156 eq572
    | exact resolve eq572 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq6605 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq241 eq2839
    | exact resolve eq2839 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq2839
  have eq6670 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq6605
       have i₂ := eq2064 sF2 sF2
       grind)
    | exact superpose eq2064 eq6605
    | exact resolve eq6605 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6605
  have eq7450 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq731 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq731
    | exact resolve eq731 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq731
  have eq7568 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7450 X0 X1
       have i₂ := eq2064 X0 X0
       grind)
    | exact superpose eq2064 eq7450
    | exact resolve eq7450 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7450
  have eq7709 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq255 X0 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq7568 (M.op x X0) y
       grind)
    | exact superpose eq7568 eq255
    | exact resolve eq255 eq7568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq7711 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq259 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq7568 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq7568 eq259
    | exact resolve eq259 eq7568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq7717 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq572 X1 X0 (M.op X0 X0)
       have i₂ := eq7568 X0 X1
       grind)
    | exact superpose eq7568 eq572
    | exact resolve eq572 eq7568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq7568
  have eq8684 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7709 (M.op x (M.op X0 x))
       have i₂ := eq1833 x X0
       grind)
    | exact superpose eq1833 eq7709
    | exact resolve eq7709 eq1833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7709
  have eq9267 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7711 (M.op sF2 (M.op x sF2))
       have i₂ := eq1833 sF2 x
       grind)
    | exact superpose eq1833 eq7711
    | exact resolve eq7711 eq1833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833 eq7711
  have eq9508 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X0 X0)) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq7717 X0 X1
       grind)
    | exact superpose eq7717 eq13
    | (have j0 := eq13 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq7717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7717
  have eq9542 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9508 X0 X1
       grind)
    | (have r₁ := eq9508 X1 X1
       have r₂ := eq2064 X1 X1
       grind)
    | exact resolve eq9508 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9508
  have eq9550 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9542 X0 X1
       have i₂ := eq2064 X1 X0
       grind)
    | exact superpose eq2064 eq9542
    | exact resolve eq9542 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9542
  have eq11160 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq233 eq9550
    | exact resolve eq9550 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq11178 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq240 eq9550
    | exact resolve eq9550 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq9550
  have eq22420 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq100 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq100
    | (have j0 := eq100 X0
       grind)
    | exact resolve eq100 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq22421 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22420 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq22420
    | (have j0 := eq22420 X0
       grind)
    | exact resolve eq22420 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq22420
  have eq22426 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq135 eq22421
    | exact resolve eq22421 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22421
  have eq22539 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq11160 eq22426
    | exact resolve eq22426 eq11160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11160 eq22426
  have eq22550 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq20 eq22539
    | exact resolve eq22539 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22539
  have eq22561 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq22550
       have i₂ := eq2064 sF0 sF0
       grind)
    | exact superpose eq2064 eq22550
    | exact resolve eq22550 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22550
  have eq22570 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq20 eq22561
    | exact resolve eq22561 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22561
  have eq22579 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq22570
       have i₂ := eq2064 sF0 sF0
       grind)
    | exact superpose eq2064 eq22570
    | exact resolve eq22570 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064 eq22570
  have eq22585 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq20 eq22579
    | exact resolve eq22579 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22579
  have eq22586 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq22585
  have eq79457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq79457
    | exact resolve eq79457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79457
  have eq79469 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq79458
       have r₂ := eq27
       grind)
    | exact resolve eq79458 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79458
  have eq79473 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq79469
    | exact resolve eq79469 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79469
  have eq79483 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq79473 eq6670
    | exact resolve eq6670 eq79473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6670 eq79473
  have eq79682 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq79483 eq11178
    | exact resolve eq11178 eq79483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11178 eq79483
  have eq79984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq79682 eq114
    | exact resolve eq114 eq79682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq79682
  have eq79994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq79984
  have eq79997 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq79994
       have r₂ := eq27
       grind)
    | exact resolve eq79994 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79994
  have eq80001 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq79997 eq73
    | exact resolve eq73 eq79997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq79997
  have eq80235 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq80001
    | exact resolve eq80001 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80001
  have eq80236 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq80235
  have eq80249 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6023
       have i₂ := eq80236
       grind)
    | exact superpose eq80236 eq6023
    | exact resolve eq6023 eq80236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6023
  have eq80426 : x ≠ (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq80236
  have eq80475 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq80249 eq135
    | exact resolve eq135 eq80249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq80249
  have eq80672 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq80475
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq80475
    | exact resolve eq80475 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80475
  have eq81505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq80672 eq22586
    | exact resolve eq22586 eq80672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22586 eq80672
  have eq81650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq81505
    | exact resolve eq81505 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81505
  have eq81667 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq81650
       have r₂ := eq27
       grind)
    | exact resolve eq81650 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81650
  have eq81672 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq81667
       grind)
    | exact superpose eq81667 eq74
    | exact resolve eq74 eq81667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81727 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8684 x
       have i₂ := eq81667
       grind)
    | exact superpose eq81667 eq8684
    | exact resolve eq8684 eq81667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8684 eq81667
  have eq81876 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6327 eq81727
    | exact resolve eq81727 eq6327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6327 eq81727
  have eq81908 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq81672
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq81672
    | exact resolve eq81672 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81672
  have eq82490 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq81876
       grind)
    | exact superpose eq81876 eq104
    | exact resolve eq104 eq81876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq81876
  have eq82681 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq82490
    | exact resolve eq82490 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq82490
  have eq83488 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq81908 eq9267
    | exact resolve eq9267 eq81908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9267 eq81908
  have eq83637 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6332 eq83488
    | exact resolve eq83488 eq6332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6332 eq83488
  have eq85206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq83637 eq82681
    | exact resolve eq82681 eq83637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82681 eq83637
  have eq85350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq85206
  have eq85365 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq85350
       have r₂ := eq27
       grind)
    | exact resolve eq85350 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85350
  have eq85369 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq85365 eq26
    | exact resolve eq26 eq85365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq85370 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq85365 eq28
    | exact resolve eq28 eq85365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq85561 : x = (M.op x y) := by
    first
    | exact superpose eq30 eq85370
    | exact resolve eq85370 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq85370
  have eq85779 : x ≠ x ∨ x = (M.op x x) := by
    first
    | exact superpose eq85561 eq80426
    | (have r₁ := eq80426
       have r₂ := eq85561
       grind)
    | exact resolve eq80426 eq85561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80426
  have eq85782 : x = (M.op x x) := by grind
  clear eq85779
  have eq86069 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq85782
       grind)
    | exact superpose eq85782 eq74
    | exact resolve eq74 eq85782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq86116 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1491 x
       have i₂ := eq85782
       grind)
    | exact superpose eq85782 eq1491
    | exact resolve eq1491 eq85782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq86293 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq86116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86116
    | exact resolve eq86116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq86116
  have eq86338 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq85365 eq86069
    | exact resolve eq86069 eq85365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86069
  have eq86355 : y = (M.op x x) := by
    first
    | exact superpose eq85561 eq86293
    | exact resolve eq86293 eq85561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85561 eq86293
  have eq86393 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq86338
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86338
    | exact resolve eq86338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86338
  have eq86399 : x = y := by
    first
    | (have i₁ := eq86355
       have i₂ := eq85782
       grind)
    | exact superpose eq85782 eq86355
    | exact resolve eq86355 eq85782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85782 eq86355
  have eq86427 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq85365 eq86393
    | exact resolve eq86393 eq85365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86393
  have eq86437 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq86399
       grind)
    | exact superpose eq86399 eq24
    | exact resolve eq24 eq86399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq86399
  have eq86758 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq86437
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86437
    | exact resolve eq86437 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq86437
  have eq86864 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq85365 eq86758
    | exact resolve eq86758 eq85365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85365 eq86758
  have eq87178 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq86864 eq85369
    | exact resolve eq85369 eq86864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85369 eq86864
  have eq90513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86427 eq87178
    | exact resolve eq87178 eq86427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86427 eq87178
  have eq90514 : False := by grind
  exact eq90514

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq492 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq536 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq492 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq537 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq536 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq543 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq537 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq537 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq537 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq552 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq543 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq543
    | (have j0 := eq543 X0 X1
       grind)
    | exact resolve eq543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq553 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq552 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq558 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq553 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq553
    | exact resolve eq553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq553 x y
       grind)
    | exact superpose eq553 eq16
    | exact resolve eq16 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq712 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq558 X0 (τ X1)
       grind)
    | exact superpose eq558 eq17
    | exact resolve eq17 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq558
  have eq726 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq712
    | exact resolve eq712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq732 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq726
    | exact resolve eq726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq746 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq569
       have i₂ := eq732 x y
       grind)
    | exact superpose eq732 eq569
    | exact resolve eq569 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq732
  have eq747 : False := by grind
  exact eq747

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  clear eq24
  have eq66 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by
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
  have eq71 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq78
    | (have j1 := eq86 y x
       grind)
    | exact resolve eq78 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq117
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118 eq86
    | (have j0 := eq86 (σ y) (σ x)
       grind)
    | exact resolve eq86 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq145 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq67
    | exact resolve eq67 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq146 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq71
    | (have r₁ := eq71
       have r₂ := eq131
       grind)
    | exact resolve eq71 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq131
  have eq419 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq418
  have eq420 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq419
       have r₂ := eq145
       grind)
    | exact resolve eq419 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq419
  have eq423 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq420 eq118
    | exact resolve eq118 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq420
  have eq427 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq423
  have eq432 : x = (M.op x y) := by
    first
    | (have r₁ := eq427
       have r₂ := eq146
       grind)
    | exact resolve eq427 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq427
  have eq435 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq432 eq20
    | exact resolve eq20 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq439 : x ≠ y ∨ x = (k y x) := by
    first
    | exact superpose eq432 eq66
    | exact resolve eq66 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq440 : x ≠ x ∨ x = y ∨ x = (k y x) := by
    first
    | exact superpose eq432 eq70
    | (have r₁ := eq70
       have r₂ := eq432
       grind)
    | exact resolve eq70 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq432
  have eq447 : x = y ∨ x = (k y x) := by grind
  clear eq440
  have eq454 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq435
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq435
    | exact resolve eq435 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq537 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq454 eq26
    | exact resolve eq26 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq957 : x = (k y x) := by
    first
    | (have r₁ := eq447
       have r₂ := eq439
       grind)
    | exact resolve eq447 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq447
  have eq961 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq957
       grind)
    | exact superpose eq957 eq78
    | exact resolve eq78 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq957
  have eq968 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq454 eq961
    | exact resolve eq961 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq970 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq968
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq968
    | exact resolve eq968 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq968
  have eq971 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq454 eq970
    | exact resolve eq970 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq970
  have eq974 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq971 eq86
    | (have j0 := eq86 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq86 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq971
  have eq975 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq974
  have eq977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq537 eq975
    | exact resolve eq975 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq975
  have eq980 : False := by grind
  exact eq980

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxx_x_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op y X0)) = X0 := by
    intro X0
    first
    | exact superpose eq189 eq16
    | exact resolve eq16 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq196 eq16
    | exact resolve eq16 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq201 eq16
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq207 eq16
    | exact resolve eq16 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : (M.op x x) = (M.op (M.op (M.op x y) (M.op x x)) (M.op (M.op x y) (M.op x x))) := by
    first
    | exact superpose eq185 eq185
    | exact resolve eq185 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq630 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq683 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq733 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 (M.op x X0)) X0) := by
    intro X0
    first
    | exact superpose eq174 eq188
    | exact resolve eq188 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq736 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq184 eq188
    | exact resolve eq188 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq744 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X1 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq188 eq16
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq825 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq197 eq197
    | exact resolve eq197 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 (M.op (σ x) X0)) X0) := by
    intro X0
    first
    | exact superpose eq175 eq200
    | exact resolve eq200 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq916 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq196 eq200
    | exact resolve eq200 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq200
  have eq931 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq916 eq16
    | exact resolve eq16 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 : G, (M.op (M.op x X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op x X0)
       have i₂ := eq733 X0
       grind)
    | exact superpose eq733 eq16
    | exact resolve eq16 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq1132 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op X0 X0) x X0
       have i₂ := eq1115 X0
       grind)
    | exact superpose eq1115 eq16
    | exact resolve eq16 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 (M.op y (M.op x y))) y)) := by
    intro X0
    first
    | exact superpose eq736 eq744
    | exact resolve eq744 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq1166 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (σ y))) := by
    intro X0
    first
    | exact superpose eq916 eq744
    | exact resolve eq744 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | (have i₁ := eq744 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq744
    | (have j0 := eq744 x X0 y
       grind)
    | exact resolve eq744 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1179 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq744
    | (have j0 := eq744 (σ x) X0 (σ y)
       grind)
    | exact resolve eq744 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq744 X0 (M.op x X1) (M.op X1 X0)
       have i₂ := eq593 X1 X0
       grind)
    | exact superpose eq593 eq744
    | exact resolve eq744 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq744
  have eq1655 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq189 eq177
    | exact resolve eq177 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1665 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq201 eq177
    | exact resolve eq177 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq1673 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) := by
    intro X0
    first
    | exact superpose eq931 eq177
    | exact resolve eq177 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq931
  have eq1829 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq912 eq16
    | exact resolve eq16 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq1864 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq1829 eq16
    | exact resolve eq16 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2233 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq195 eq1161
    | exact resolve eq1161 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq1161
  have eq2334 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq207 eq1166
    | exact resolve eq1166 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq1166
  have eq2652 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq627
       grind)
    | exact superpose eq627 eq39
    | exact resolve eq39 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq2653 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2652
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2652
    | exact resolve eq2652 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652
  have eq2655 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2653
    | exact resolve eq2653 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2653
  have eq2749 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 (M.op X0 X1)
       have i₂ := eq1234 X1 X0
       grind)
    | exact superpose eq1234 eq16
    | exact resolve eq16 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq2858 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2749 X1 (M.op X0 X0)
       have i₂ := eq2749 X0 X0
       grind)
    | exact superpose eq2749 eq2749
    | exact resolve eq2749 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3887 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1132 (M.op x x)
       have i₂ := eq2749 x x
       grind)
    | exact superpose eq2749 eq1132
    | exact resolve eq1132 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq4006 : y = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq3887 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3887
    | (have j0 := eq3887 y
       grind)
    | exact resolve eq3887 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4011 : (M.op (M.op x y) (M.op x x)) = (M.op (M.op (M.op (M.op x y) (M.op x x)) (M.op (M.op x y) (M.op x x))) (M.op x x)) := by
    first
    | exact superpose eq185 eq3887
    | exact resolve eq3887 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq3887
  have eq4060 : (M.op (M.op x y) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq590 eq4011
    | exact resolve eq4011 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq4011
  have eq4062 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq4060
       have i₂ := eq1115 x
       grind)
    | exact superpose eq1115 eq4060
    | exact resolve eq4060 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060
  have eq4065 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq4006 eq1655
    | exact resolve eq1655 eq4006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655 eq4006
  have eq4460 : x ≠ (M.op x y) ∨ (M.op (M.op x x) (M.op x x)) = (k (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq4062 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq4062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4062
  have eq4480 : x ≠ (M.op x y) ∨ x = (k (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq4460
       have i₂ := eq1115 x
       grind)
    | exact superpose eq1115 eq4460
    | exact resolve eq4460 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq4460
  have eq4491 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4065 eq11
    | (have j0 := eq11 (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq11 eq4065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065
  have eq4513 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq4491
       have i₂ := eq2749 sF0 sF0
       grind)
    | exact superpose eq2749 eq4491
    | exact resolve eq4491 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4491
  have eq4514 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq4513
  have eq5389 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) := by
    first
    | exact superpose eq324 eq1673
    | exact resolve eq1673 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq1673
  have eq5428 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq916 eq5389
    | exact resolve eq5389 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916 eq5389
  have eq5429 : (σ y) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5428
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq5428
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq5428 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5431 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq5428 eq1665
    | exact resolve eq1665 eq5428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665 eq5428
  have eq5461 : (σ y) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5429
  have eq5477 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5431 eq11
    | (have j0 := eq11 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq11 eq5431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5431
  have eq5503 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5477
       have i₂ := eq2749 sF4 sF4
       grind)
    | exact superpose eq2749 eq5477
    | exact resolve eq5477 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5477
  have eq5504 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq5503
  have eq5582 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1864 (M.op x x)
       have i₂ := eq2749 x x
       grind)
    | exact superpose eq2749 eq1864
    | exact resolve eq1864 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864 eq2749
  have eq5736 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x)))) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq197 eq5582
    | exact resolve eq5582 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq5582
  have eq5793 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq825 eq5736
    | exact resolve eq5736 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq5736
  have eq5796 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1829 eq5793
    | exact resolve eq5793 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5793
  have eq5808 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5796 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq5796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5796
  have eq5831 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1829 eq5808
    | exact resolve eq5808 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829 eq5808
  have eq10041 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq2858 X0 X1
       grind)
    | exact superpose eq2858 eq16
    | exact resolve eq16 eq2858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq17657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2655 eq630
    | exact resolve eq630 eq2655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17671 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17657
       have r₂ := eq27
       grind)
    | exact resolve eq17657 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17657
  have eq17716 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17671 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq17671
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17671
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq17671
       grind)
    | exact resolve eq13 eq17671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17671
  have eq17748 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq17716
  have eq17769 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17748 eq141
    | exact resolve eq141 eq17748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq17748
  have eq17784 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq17769
    | exact resolve eq17769 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17769
  have eq17787 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq685 x
       grind)
    | (have r₁ := eq17784
       have r₂ := eq685 x
       grind)
    | exact resolve eq17784 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq17784
  have eq17815 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1171 x
       have i₂ := eq17787
       grind)
    | exact superpose eq17787 eq1171
    | exact resolve eq1171 eq17787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17831 : x ≠ x ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq17787
       grind)
    | exact superpose eq17787 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq17787
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17787
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17787
       grind)
    | exact resolve eq13 eq17787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17787
  have eq17863 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17831
  have eq17875 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17815
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17815
    | exact resolve eq17815 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17815
  have eq17883 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq17863
       grind)
    | exact superpose eq17863 eq39
    | exact resolve eq39 eq17863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq17863
  have eq17898 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17883
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17883
    | exact resolve eq17883 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17883
  have eq17914 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17875 eq4514
    | exact resolve eq4514 eq17875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17980 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17875 eq10041
    | exact resolve eq10041 eq17875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17875
  have eq17994 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17898 eq684
    | (have j0 := eq684 (σ x) (σ x)
       grind)
    | (have r₁ := eq684 (σ x) (σ x)
       have r₂ := eq17898
       grind)
    | exact resolve eq684 eq17898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17898
  have eq17995 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17994
  have eq17996 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17995
  have eq18125 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq17980
       grind)
    | exact superpose eq17980 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17980
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17980
       grind)
    | exact resolve eq13 eq17980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17980
  have eq18161 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18125
       have r₂ := eq17914
       grind)
    | exact resolve eq18125 eq17914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17914 eq18125
  have eq18188 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17996 eq1179
    | exact resolve eq1179 eq17996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq17996
  have eq18248 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18188
    | exact resolve eq18188 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18188
  have eq18276 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq18161
       grind)
    | exact superpose eq18161 eq40
    | exact resolve eq40 eq18161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18161
  have eq18288 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18276
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18276
    | exact resolve eq18276 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18276
  have eq18290 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq18288
    | exact resolve eq18288 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18288
  have eq18367 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18248 eq5504
    | exact resolve eq5504 eq18248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504
  have eq18435 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18248 eq10041
    | exact resolve eq10041 eq18248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18248
  have eq18440 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18290 eq18367
    | exact resolve eq18367 eq18290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18367
  have eq18442 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18440
       have r₂ := eq27
       grind)
    | exact resolve eq18440 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18440
  have eq18762 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18435 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18435
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18435
       grind)
    | exact resolve eq13 eq18435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18435
  have eq18799 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18762
       have r₂ := eq18442
       grind)
    | exact resolve eq18762 eq18442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18442 eq18762
  have eq18802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18290 eq18799
    | exact resolve eq18799 eq18290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18290 eq18799
  have eq18803 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18802
       have r₂ := eq27
       grind)
    | exact resolve eq18802 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18802
  have eq18805 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18803 eq27
    | exact resolve eq27 eq18803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18860 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18803 eq2334
    | exact resolve eq2334 eq18803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq18900 : (σ x) ≠ (σ x) ∨ (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18803 eq5831
    | (have r₁ := eq5831
       have r₂ := eq18803
       grind)
    | exact resolve eq5831 eq18803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5831
  have eq18911 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18900
  have eq18920 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18860
    | exact resolve eq18860 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18860
  have eq18938 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18803 eq18920
    | exact resolve eq18920 eq18803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18803 eq18920
  have eq18996 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18938 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18997 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18938 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq18938
       grind)
    | exact resolve eq13 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19031 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq18996
  have eq19042 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19031
       have r₂ := eq18997
       grind)
    | exact resolve eq19031 eq18997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18997 eq19031
  have eq19153 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19042 eq97
    | exact resolve eq97 eq19042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq19042
  have eq19171 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq19153
    | exact resolve eq19153 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq19153
  have eq19807 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18938 eq18911
    | exact resolve eq18911 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18911 eq18938
  have eq19821 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19807
  have eq19829 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19821 eq2655
    | exact resolve eq2655 eq19821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655 eq19821
  have eq19841 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq19829
  have eq19848 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19841
       have r₂ := eq18805
       grind)
    | exact resolve eq19841 eq18805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18805 eq19841
  have eq19891 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1171 x
       have i₂ := eq19848
       grind)
    | exact superpose eq19848 eq1171
    | exact resolve eq1171 eq19848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq19907 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq19848
       grind)
    | exact superpose eq19848 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq19848
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19848
       grind)
    | exact resolve eq13 eq19848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19939 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq19907
  have eq19952 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19891
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19891
    | exact resolve eq19891 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19891
  have eq20019 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19171
       have i₂ := eq19939
       grind)
    | exact superpose eq19939 eq19171
    | exact resolve eq19171 eq19939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19171 eq19939
  have eq20037 : x = (M.op x y) ∨ x = y := by grind
  clear eq20019
  have eq20215 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19952 eq10041
    | exact resolve eq10041 eq19952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19952
  have eq20218 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20037 eq20215
    | exact resolve eq20215 eq20037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20037 eq20215
  have eq20606 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19848
       have i₂ := eq20218
       grind)
    | exact superpose eq20218 eq19848
    | exact resolve eq19848 eq20218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19848 eq20218
  have eq20678 : x = (M.op x y) := by grind
  clear eq20606
  have eq20685 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20678
       grind)
    | exact superpose eq20678 eq18
    | exact resolve eq18 eq20678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20686 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq20678
       grind)
    | exact superpose eq20678 eq22
    | exact resolve eq22 eq20678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq20738 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq4480
       have i₂ := eq20678
       grind)
    | exact superpose eq20678 eq4480
    | (have r₁ := eq4480
       have r₂ := eq20678
       grind)
    | exact resolve eq4480 eq20678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4480 eq20678
  have eq20746 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by grind
  clear eq20738
  have eq20750 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20686 eq20
    | exact resolve eq20 eq20686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20686
  have eq20835 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20685 eq2233
    | exact resolve eq2233 eq20685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233 eq20685
  have eq20924 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20835 eq4514
    | exact resolve eq4514 eq20835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4514
  have eq20956 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20835 eq11
    | exact resolve eq11 eq20835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20957 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20835 eq13
    | exact resolve eq13 eq20835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20990 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20835 eq10041
    | exact resolve eq10041 eq20835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10041
  have eq20991 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq20956
  have eq20994 : y = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq20991
       have r₂ := eq20957
       grind)
    | exact resolve eq20991 eq20957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20957 eq20991
  have eq21143 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq20990
       grind)
    | exact superpose eq20990 eq13
    | exact resolve eq13 eq20990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20990
  have eq21179 : (M.op x y) = (k y y) := by
    first
    | (have r₁ := eq21143
       have r₂ := eq20924
       grind)
    | exact resolve eq21143 eq20924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20924 eq21143
  have eq21185 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20994 eq37
    | exact resolve eq37 eq20994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq20994
  have eq21199 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq21185
    | exact resolve eq21185 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21185
  have eq21201 : (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20750 eq21199
    | exact resolve eq21199 eq20750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21199
  have eq21203 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21201
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21201
    | exact resolve eq21201 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21201
  have eq21211 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq21179
       grind)
    | exact superpose eq21179 eq40
    | exact resolve eq40 eq21179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq21179
  have eq21225 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq21211
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21211
    | exact resolve eq21211 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21211
  have eq21227 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq21225
    | exact resolve eq21225 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21225
  have eq21229 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq20750 eq21227
    | exact resolve eq21227 eq20750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21227
  have eq21274 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21229 eq684
    | (have j0 := eq684 (σ y) (σ y)
       grind)
    | exact resolve eq684 eq21229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq21275 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq21274
  have eq21350 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq20746 eq41
    | exact resolve eq41 eq20746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq20746
  have eq21358 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq20750 eq21350
    | exact resolve eq21350 eq20750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21350
  have eq21360 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20835 eq21358
    | exact resolve eq21358 eq20835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20835 eq21358
  have eq21361 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq21360
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21360
    | exact resolve eq21360 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq21360
  have eq21362 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq21361
    | exact resolve eq21361 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq21361
  have eq21363 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20750 eq21362
    | exact resolve eq21362 eq20750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21362
  have eq21368 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21363 eq630
    | exact resolve eq630 eq21363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq21363
  have eq21378 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21368
  have eq22992 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21378 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq21378
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21378
       grind)
    | exact resolve eq13 eq21378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21378
  have eq23024 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22992
  have eq23035 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21203 eq23024
    | exact resolve eq23024 eq21203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21203 eq23024
  have eq23212 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23035 eq27
    | exact resolve eq27 eq23035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23288 : (σ y) = (M.op (k (σ y) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23035 eq5461
    | exact resolve eq5461 eq23035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5461 eq23035
  have eq23338 : (σ y) = (M.op (k (σ y) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq23288
       have r₂ := eq21275
       grind)
    | exact resolve eq23288 eq21275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21275 eq23288
  have eq23356 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq23212
       have r₂ := eq20750
       grind)
    | exact resolve eq23212 eq20750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23212
  have eq23366 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21229 eq23338
    | exact resolve eq23338 eq21229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21229 eq23338
  have eq23384 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq23356 eq23366
    | exact resolve eq23366 eq23356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23366
  have eq23386 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23356 eq23384
    | exact resolve eq23384 eq23356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23384
  have eq23387 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq23386
  have eq23390 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23356 eq26
    | exact resolve eq26 eq23356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq23356
  have eq23535 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23387 eq23390
    | exact resolve eq23390 eq23387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23387 eq23390
  have eq23562 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq23535 eq27
    | exact resolve eq27 eq23535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23535
  have eq23749 : False := by grind
  exact eq23749

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq56 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq420 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq745 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1678 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq419 eq410
    | exact resolve eq410 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq1682 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq420 eq410
    | exact resolve eq410 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq420
  have eq55291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq55291
    | exact resolve eq55291 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55291
  have eq55307 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq55302
       have r₂ := eq28
       grind)
    | exact resolve eq55302 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55302
  have eq55309 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq55307
    | exact resolve eq55307 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55307
  have eq55337 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq55309
  have eq55450 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq55337
    | exact resolve eq55337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55337
  have eq56287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq55450 eq98
    | exact resolve eq98 eq55450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55450
  have eq56302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56287
  have eq56304 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq56302
       have r₂ := eq28
       grind)
    | exact resolve eq56302 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56302
  have eq56334 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56304
  have eq56447 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56334
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56334
    | exact resolve eq56334 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56334
  have eq57339 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq56447
       grind)
    | exact superpose eq56447 eq73
    | exact resolve eq73 eq56447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56447
  have eq57373 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq57339
    | exact resolve eq57339 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57339
  have eq58055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57373 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq57373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq58055
    | exact resolve eq58055 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58055
  have eq58073 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq58068
       have r₂ := eq28
       grind)
    | exact resolve eq58068 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58068
  have eq58075 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq58073
    | exact resolve eq58073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58073
  have eq58076 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq58075
  have eq58105 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq58076
  have eq58218 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq58105
    | exact resolve eq58105 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58105
  have eq58830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58218 eq57373
    | exact resolve eq57373 eq58218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57373 eq58218
  have eq58842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq58830
  have eq58846 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq58842
       have r₂ := eq28
       grind)
    | exact resolve eq58842 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58842
  have eq58893 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58846 eq1682
    | exact resolve eq1682 eq58846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682
  have eq58956 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq58893
    | exact resolve eq58893 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58893
  have eq58965 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58846 eq58956
    | exact resolve eq58956 eq58846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58846 eq58956
  have eq59089 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq58965
  have eq59252 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq59089
  have eq59365 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq59252
    | exact resolve eq59252 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59252
  have eq59652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59365 eq98
    | exact resolve eq98 eq59365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq59666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq59652
  have eq59669 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq59666
       have r₂ := eq28
       grind)
    | exact resolve eq59666 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59666
  have eq59700 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq59669
  have eq59813 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59700
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59700
    | exact resolve eq59700 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59700
  have eq60351 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq59813
       grind)
    | exact superpose eq59813 eq73
    | exact resolve eq73 eq59813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59813
  have eq60385 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq60351
    | exact resolve eq60351 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60351
  have eq60441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60385 eq59365
    | exact resolve eq59365 eq60385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59365 eq60385
  have eq60453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq60441
  have eq60459 : x = (M.op x y) := by
    first
    | (have r₁ := eq60453
       have r₂ := eq28
       grind)
    | exact resolve eq60453 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60453
  have eq60464 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq60459 eq21
    | exact resolve eq21 eq60459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq60560 : y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq60459 eq1678
    | exact resolve eq1678 eq60459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq60623 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq60560
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60560
    | exact resolve eq60560 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60560
  have eq60681 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq60464
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60464
    | exact resolve eq60464 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60464
  have eq60690 : y = (M.op x x) := by
    first
    | exact superpose eq60459 eq60623
    | exact resolve eq60623 eq60459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60623
  have eq60698 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq60681 eq27
    | exact resolve eq27 eq60681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60823 : (M.op x y) = (k y x) := by grind
  clear eq60690
  have eq60945 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq60823
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60823
    | exact resolve eq60823 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq60823
  have eq60968 : x = (k y x) := by
    first
    | exact superpose eq60459 eq60945
    | exact resolve eq60945 eq60459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60459 eq60945
  have eq61270 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq60968
       grind)
    | exact superpose eq60968 eq73
    | exact resolve eq73 eq60968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq61287 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq745 x y
       have i₂ := eq60968
       grind)
    | exact superpose eq60968 eq745
    | (have j0 := eq745 x y
       grind)
    | exact resolve eq745 eq60968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq60968
  have eq61291 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq61287
  have eq61300 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61291
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq61291
    | exact resolve eq61291 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61291
  have eq61314 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq60681 eq61270
    | exact resolve eq61270 eq60681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61270
  have eq61317 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61300
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq61300
    | exact resolve eq61300 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61300
  have eq61331 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq61314
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq61314
    | exact resolve eq61314 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61314
  have eq61334 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq61317
    | exact resolve eq61317 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq61317
  have eq61347 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq60681 eq61331
    | exact resolve eq61331 eq60681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61331
  have eq61350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq60681 eq61334
    | exact resolve eq61334 eq60681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61334
  have eq61360 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq61350
       have r₂ := eq28
       grind)
    | exact resolve eq61350 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61350
  have eq61370 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61360
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq61360
    | exact resolve eq61360 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq61360
  have eq61379 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq60681 eq61370
    | exact resolve eq61370 eq60681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60681 eq61370
  have eq61388 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq61379
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq61379
    | exact resolve eq61379 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq61379
  have eq61452 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq61388
  have eq61574 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq60698 eq61452
    | exact resolve eq61452 eq60698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60698 eq61452
  have eq61575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq61347 eq61574
    | exact resolve eq61574 eq61347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61347 eq61574
  have eq61576 : False := by grind
  exact eq61576

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (k X1 (k y X0))) = (k (σ X1) (k (σ y) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq10
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (k (k y X0) X1)) = (k (k (σ y) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k y X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq10
    | exact resolve eq10 eq36
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
  have eq49 : ∀ X0 X1 : G, (σ (k (k (M.op x y) X0) X1)) = (k (k (σ (M.op x y)) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq37 eq10
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op y X0)) = X0 := by
    intro X0
    first
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq190 eq16
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq194 eq16
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq198 eq16
    | exact resolve eq16 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (τ X0) X1) X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq575 : (M.op x x) = (M.op (M.op (M.op x y) (M.op x x)) (M.op (M.op x y) (M.op x x))) := by
    first
    | exact superpose eq182 eq182
    | exact resolve eq182 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 (M.op x X0)) X0) := by
    intro X0
    first
    | exact superpose eq174 eq184
    | exact resolve eq184 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq621 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq181 eq184
    | exact resolve eq184 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq625 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X1 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq643 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq646 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq705 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq709 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq650 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq730 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq709 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq709 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq709 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq709 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq823 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq730 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq730
    | (have j0 := eq730 (σ X0) X1
       grind)
    | exact resolve eq730 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq191 eq191
    | exact resolve eq191 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 (M.op (σ x) X0)) X0) := by
    intro X0
    first
    | exact superpose eq175 eq193
    | exact resolve eq193 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op X0 (M.op (σ y) X0)) X0) := by
    intro X0
    first
    | exact superpose eq198 eq193
    | exact resolve eq193 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq190 eq193
    | exact resolve eq193 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq193
  have eq933 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq918 eq16
    | exact resolve eq16 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : ∀ X0 : G, (M.op (M.op x X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op x X0)
       have i₂ := eq618 X0
       grind)
    | exact superpose eq618 eq16
    | exact resolve eq16 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq1134 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op X0 X0) x X0
       have i₂ := eq1117 X0
       grind)
    | exact superpose eq1117 eq16
    | exact resolve eq16 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 (M.op y (M.op x y))) y)) := by
    intro X0
    first
    | exact superpose eq621 eq625
    | exact resolve eq625 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq1166 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (σ y))) := by
    intro X0
    first
    | exact superpose eq918 eq625
    | exact resolve eq625 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | (have i₁ := eq625 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq625
    | (have j0 := eq625 x X0 y
       grind)
    | exact resolve eq625 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1179 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq625
    | (have j0 := eq625 (σ x) X0 (σ y)
       grind)
    | exact resolve eq625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 (M.op x X1) (M.op X1 X0)
       have i₂ := eq577 X1 X0
       grind)
    | exact superpose eq577 eq625
    | exact resolve eq625 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq625
  have eq1426 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq914 eq16
    | exact resolve eq16 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq1673 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1686 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq185 eq177
    | exact resolve eq177 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1696 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq194 eq177
    | exact resolve eq177 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq1704 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) := by
    intro X0
    first
    | exact superpose eq933 eq177
    | exact resolve eq177 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq1733 : ∀ X0 : G, y = (M.op (M.op (M.op X0 x) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq177 x X0 x
       grind)
    | exact superpose eq177 eq178
    | exact resolve eq178 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq178
  have eq1864 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq1426 eq16
    | exact resolve eq16 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2231 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq189 eq1161
    | exact resolve eq1161 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq1161
  have eq2332 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq198 eq1166
    | exact resolve eq1166 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq1166
  have eq2736 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 (M.op X0 X1)
       have i₂ := eq1234 X1 X0
       grind)
    | exact superpose eq1234 eq16
    | exact resolve eq16 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2766 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq643
       grind)
    | exact superpose eq643 eq39
    | exact resolve eq39 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq2767 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2766
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2766
    | exact resolve eq2766 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq2769 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2767
    | exact resolve eq2767 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767
  have eq2856 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2736 X1 (M.op X0 X0)
       have i₂ := eq2736 X0 X0
       grind)
    | exact superpose eq2736 eq2736
    | exact resolve eq2736 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2877 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq2736 X0 X0
       grind)
    | exact superpose eq2736 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3877 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1134 (M.op x x)
       have i₂ := eq2736 x x
       grind)
    | exact superpose eq2736 eq1134
    | exact resolve eq1134 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3930 : (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq182 (M.op sF0 sF0)
       have i₂ := eq1134 sF0
       grind)
    | exact superpose eq1134 eq182
    | exact resolve eq182 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq3956 : (M.op x y) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq3930
       have i₂ := eq2736 sF0 sF0
       grind)
    | exact superpose eq2736 eq3930
    | exact resolve eq3930 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3930
  have eq3968 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3956 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3969 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq3956 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq3987 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) ∨ x ≠ (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3969
       have i₂ := eq2736 sF0 sF0
       grind)
    | exact superpose eq2736 eq3969
    | exact resolve eq3969 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3969
  have eq3989 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq3987
       have r₂ := eq3968
       grind)
    | exact resolve eq3987 eq3968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968 eq3987
  have eq3995 : y = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq3877 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3877
    | (have j0 := eq3877 y
       grind)
    | exact resolve eq3877 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4000 : (M.op (M.op x y) (M.op x x)) = (M.op (M.op (M.op (M.op x y) (M.op x x)) (M.op (M.op x y) (M.op x x))) (M.op x x)) := by
    first
    | exact superpose eq182 eq3877
    | exact resolve eq3877 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq3877
  have eq4048 : (M.op (M.op x y) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq575 eq4000
    | exact resolve eq4000 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq4000
  have eq4049 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq4048
       have i₂ := eq1117 x
       grind)
    | exact superpose eq1117 eq4048
    | exact resolve eq4048 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117 eq4048
  have eq4052 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq3995 eq1686
    | exact resolve eq1686 eq3995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq4057 : y = (k (M.op x y) (M.op y y)) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) (M.op y y)) := by
    first
    | exact superpose eq3995 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq3995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3995
  have eq4077 : y = (M.op y y) ∨ y = (k (M.op x y) (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4057
       have i₂ := eq2736 y y
       grind)
    | exact superpose eq2736 eq4057
    | exact resolve eq4057 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4057
  have eq4078 : y = (k (M.op x y) (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq4077
  have eq4088 : ∀ X0 : G, (M.op (M.op x X0) (M.op (M.op x y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq4049 eq16
    | exact resolve eq16 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4049
  have eq4115 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq4052 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq4052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4052
  have eq4135 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq4115
       have i₂ := eq2736 sF0 sF0
       grind)
    | exact superpose eq2736 eq4115
    | exact resolve eq4115 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115
  have eq4136 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq4135
  have eq4979 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) := by
    first
    | exact superpose eq310 eq1704
    | exact resolve eq1704 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310 eq1704
  have eq5015 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq918 eq4979
    | exact resolve eq4979 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq4979
  have eq5018 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq5015 eq1696
    | exact resolve eq1696 eq5015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq5024 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5015 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq5015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5015
  have eq5048 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5024
       have i₂ := eq2736 sF3 sF3
       grind)
    | exact superpose eq2736 eq5024
    | exact resolve eq5024 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024
  have eq5049 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5048
  have eq5060 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5018 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq5018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5018
  have eq5084 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5060
       have i₂ := eq2736 sF4 sF4
       grind)
    | exact superpose eq2736 eq5060
    | exact resolve eq5060 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5060
  have eq5085 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq5084
  have eq5157 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1864 (M.op x x)
       have i₂ := eq2736 x x
       grind)
    | exact superpose eq2736 eq1864
    | exact resolve eq1864 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864 eq2736
  have eq5305 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x)))) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq191 eq5157
    | exact resolve eq5157 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq5157
  have eq5357 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq827 eq5305
    | exact resolve eq5305 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq5305
  have eq5359 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1426 eq5357
    | exact resolve eq5357 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5357
  have eq5360 : (σ x) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5359
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq5359
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq5359 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5370 : (σ x) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5359 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq5359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5371 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5359 eq12
    | (have j0 := eq12 (M.op (σ x) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq5359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5359
  have eq5391 : (σ x) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5360
  have eq5392 : (σ x) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1426 eq5371
    | exact resolve eq5371 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426 eq5371
  have eq5394 : (σ x) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq5392
       have r₂ := eq5370
       grind)
    | exact resolve eq5392 eq5370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5370 eq5392
  have eq9352 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq2856 X0 X1
       grind)
    | exact superpose eq2856 eq16
    | exact resolve eq16 eq2856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856
  have eq15735 : (σ y) = (k (M.op (σ x) (σ y)) (k (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5049
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq5049
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq5049 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5049
  have eq15740 : (σ y) = (k (M.op (σ x) (σ y)) (k (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq15735
  have eq15741 : (σ y) = (k (M.op (σ x) (σ y)) (k (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq15740
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq15740 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15740
  have eq15842 : y = (k (M.op x y) (k y y)) ∨ y = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4078
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq4078
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq4078 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4078
  have eq15848 : y = (k (M.op x y) (k y y)) ∨ y = (k y y) ∨ y = (M.op y y) := by grind
  clear eq15842
  have eq15850 : y = (k (M.op x y) (k y y)) ∨ y = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq15848
       have r₂ := eq13 x y
       grind)
    | exact resolve eq15848 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15848
  have eq16070 : (σ y) = (k (σ (M.op x y)) (σ (k y y))) ∨ y = (k y y) := by
    first
    | exact superpose eq15850 eq37
    | exact resolve eq37 eq15850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15850
  have eq16074 : (σ y) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16070
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq16070
    | exact resolve eq16070 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16070
  have eq16075 : (σ y) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16074
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16074
    | exact resolve eq16074 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16074
  have eq17078 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1673 (M.op sF4 X0) X0
       have i₂ := eq16 X0 sF4 (M.op sF4 X0)
       grind)
    | exact superpose eq16 eq1673
    | exact resolve eq1673 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq17681 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2769 eq646
    | exact resolve eq646 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq17694 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17681
       have r₂ := eq27
       grind)
    | exact resolve eq17681 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17681
  have eq17737 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq17694 eq2877
    | (have r₁ := eq2877 (σ x) x
       have r₂ := eq17694
       grind)
    | (have r₁ := eq2877 x x
       have r₂ := eq17694
       grind)
    | exact resolve eq2877 eq17694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17694
  have eq17772 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq17737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17737
  have eq17919 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2877 x X1
       have i₂ := eq17772 X0
       grind)
    | exact superpose eq17772 eq2877
    | (have j1 := eq17772 X1
       grind)
    | (have r₁ := eq2877 x X1
       have r₂ := eq17772 X0
       grind)
    | exact resolve eq2877 eq17772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17772
  have eq17954 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17919 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17919
  have eq18195 : ∀ X0 : G, (τ (σ x)) = (k x (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq17954 (k sF2 X0) x
       grind)
    | exact superpose eq17954 eq90
    | (have j1 := eq17954 X0 x
       grind)
    | exact resolve eq90 eq17954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq17954
  have eq18210 : ∀ X0 : G, x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq18195
    | (have j0 := eq18195 x
       grind)
    | exact resolve eq18195 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18195
  have eq18224 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18210 X0
       have j1 := eq730 x X0
       grind)
    | (have r₁ := eq18210 X0
       have r₂ := eq730 x x
       grind)
    | (have r₁ := eq18210 x
       have r₂ := eq730 x x
       grind)
    | exact resolve eq18210 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq18210
  have eq18233 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq706 x
       have i₂ := eq18224 x
       grind)
    | exact superpose eq18224 eq706
    | (have j0 := eq706 x
       grind)
    | (have r₁ := eq706 x
       have r₂ := eq18224 x
       grind)
    | exact resolve eq706 eq18224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq18241 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq18224 x
       grind)
    | exact superpose eq18224 eq35
    | exact resolve eq35 eq18224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18224
  have eq18249 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18233
  have eq18258 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18241
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18241
    | exact resolve eq18241 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18241
  have eq18291 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1171 x
       have i₂ := eq18249
       grind)
    | exact superpose eq18249 eq1171
    | exact resolve eq1171 eq18249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171 eq18249
  have eq18352 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18291
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18291
    | exact resolve eq18291 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18291
  have eq18368 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18258 eq704
    | (have j0 := eq704 (σ x) (σ x)
       grind)
    | (have r₁ := eq704 (σ x) (σ x)
       have r₂ := eq18258
       grind)
    | exact resolve eq704 eq18258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18258
  have eq18369 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18368
  have eq18370 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18369
  have eq18499 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18352 eq4136
    | exact resolve eq4136 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18528 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18352 eq2877
    | exact resolve eq2877 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18604 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18370 eq1179
    | exact resolve eq1179 eq18370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq18370
  have eq18665 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18604
    | exact resolve eq18604 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18604
  have eq18834 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18665 eq5085
    | exact resolve eq5085 eq18665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5085
  have eq18866 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18665 eq2877
    | exact resolve eq2877 eq18665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22499 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq18499
       grind)
    | exact superpose eq18499 eq40
    | exact resolve eq40 eq18499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18499
  have eq22511 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22499
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22499
    | exact resolve eq22499 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22499
  have eq22514 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22511
    | exact resolve eq22511 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22511
  have eq22881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22514 eq18834
    | exact resolve eq18834 eq22514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22881
  have eq22899 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22893
       have r₂ := eq27
       grind)
    | exact resolve eq22893 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22893
  have eq22908 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22899 eq27
    | exact resolve eq27 eq22899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23017 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22899 eq18665
    | exact resolve eq18665 eq22899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18665
  have eq23024 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22899 eq18866
    | (have j0 := eq18866 X0
       grind)
    | (have r₁ := eq18866 X0
       have r₂ := eq22899
       grind)
    | exact resolve eq18866 eq22899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18866
  have eq23031 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22899
  have eq23038 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23024
  have eq23039 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23038 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23038
  have eq23047 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23017
  have eq23053 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23039 X0
       grind)
    | (have r₁ := eq23039 X0
       have r₂ := eq23031
       grind)
    | exact resolve eq23039 eq23031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23039
  have eq23059 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq23047
       have r₂ := eq23031
       grind)
    | exact resolve eq23047 eq23031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23031 eq23047
  have eq23183 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23053 eq22514
    | exact resolve eq22514 eq23053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22514
  have eq23184 : (τ (σ y)) = (k y (τ (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23053 eq107
    | exact resolve eq107 eq23053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq23053
  have eq23185 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23183
  have eq23192 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq23184
    | exact resolve eq23184 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23184
  have eq23193 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq23185
       have r₂ := eq22908
       grind)
    | exact resolve eq23185 eq22908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22908 eq23185
  have eq23208 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq18528 y
       grind)
    | (have r₁ := eq23192
       have r₂ := eq18528 x
       grind)
    | exact resolve eq23192 eq18528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18528 eq23192
  have eq23214 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23193 eq23208
    | exact resolve eq23208 eq23193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23208
  have eq23368 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23214 eq823
    | (have j0 := eq823 (M.op x y) X0
       grind)
    | exact resolve eq823 eq23214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23373 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23214 eq704
    | (have j0 := eq704 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq704 (M.op x y) (M.op x y)
       have r₂ := eq23214
       grind)
    | exact resolve eq704 eq23214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq23214
  have eq23374 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23373
  have eq23375 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23374
  have eq23380 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq23368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23368
  have eq23383 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq23380
    | (have j0 := eq23380 X0
       grind)
    | exact resolve eq23380 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23380
  have eq23545 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23375 eq9352
    | exact resolve eq9352 eq23375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23375
  have eq23646 : ∀ X0 : G, (σ (σ (M.op x y))) ≠ (σ (σ (M.op x y))) ∨ (k X0 (σ (σ (M.op x y)))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23383 eq823
    | (have j0 := eq823 (σ (M.op x y)) X0
       grind)
    | exact resolve eq823 eq23383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23669 : ∀ X0 : G, (k X0 (σ (σ (M.op x y)))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq23646 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23646
  have eq24097 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (k y (σ (M.op x y))) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23669 eq46
    | exact resolve eq46 eq23669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq24098 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (k y (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23669 eq45
    | exact resolve eq45 eq23669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq23669
  have eq24106 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (k (M.op x y) (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23193 eq24098
    | exact resolve eq24098 eq23193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24098
  have eq24107 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (k (M.op x y) (σ (M.op x y))) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23193 eq24097
    | exact resolve eq24097 eq23193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24097
  have eq24130 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23383 eq24106
    | exact resolve eq24106 eq23383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24106
  have eq24131 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23383 eq24107
    | exact resolve eq24107 eq23383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24107
  have eq24142 : ∀ X0 : G, (k (σ X0) (σ y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq24130
    | exact resolve eq24130 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq24130
  have eq24143 : ∀ X0 : G, (k (σ y) (σ X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq24131
    | exact resolve eq24131 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24131
  have eq24149 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23383 eq24142
    | exact resolve eq24142 eq23383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23383 eq24142
  have eq26093 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23545 eq1234
    | exact resolve eq1234 eq23545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq26101 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23545 eq915
    | exact resolve eq915 eq23545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq23545
  have eq26152 : y = (M.op (σ y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18352 eq26101
    | exact resolve eq26101 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26101
  have eq26160 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18352 eq26093
    | exact resolve eq26093 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26093
  have eq26187 : (M.op x y) = (M.op (σ y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23193 eq26152
    | exact resolve eq26152 eq23193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26152
  have eq26195 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23193 eq26160
    | exact resolve eq26160 eq23193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26160
  have eq26294 : (M.op x y) = (k (M.op x y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26187 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq26187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26295 : (M.op x y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26187 eq12
    | (have j0 := eq12 (M.op x y) (σ y)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq26187
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26187
       grind)
    | exact resolve eq12 eq26187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26187
  have eq26337 : (M.op x y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18352 eq26295
    | exact resolve eq26295 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26295
  have eq26338 : (M.op x y) = (k (M.op x y) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (M.op x y) (σ y)
       grind)
    | (have r₁ := eq26294
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq26294 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26294
  have eq26341 : (M.op x y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23059 eq26337
    | exact resolve eq26337 eq23059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23059 eq26337
  have eq26343 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (k (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (M.op x y) (σ y)
       grind)
    | (have r₁ := eq26341
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq26341 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26341
  have eq26344 : (M.op x y) = (k (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26343
       have r₂ := eq26338
       grind)
    | exact resolve eq26343 eq26338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26338 eq26343
  have eq26469 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ (M.op x y) = X0 ∨ (M.op X0 X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26195 eq11
    | (have j0 := eq11 X0 X0
       grind)
    | exact resolve eq11 eq26195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26470 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op x y) X0) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26195 eq12
    | (have j0 := eq12 (M.op x y) X0
       grind)
    | (have r₁ := eq12 (M.op x y) (M.op x y)
       have r₂ := eq26195 (M.op x y)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq26195 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26195 X0
       grind)
    | exact resolve eq12 eq26195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26195
  have eq26750 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ y = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18352 eq26470
    | (have j0 := eq26470 X0
       grind)
    | (have r₁ := eq26470 x
       have r₂ := eq18352
       grind)
    | exact resolve eq26470 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18352 eq26470
  have eq26751 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ (M.op x y) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq26469 X0
       have j1 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq26469 (M.op (M.op x y) (M.op x y))
       have r₂ := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq26469 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq26469 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26469
  have eq26754 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23193 eq26750
    | (have j0 := eq26750 X0
       grind)
    | (have r₁ := eq26750 x
       have r₂ := eq23193
       grind)
    | (have r₁ := eq26750 y
       have r₂ := eq23193
       grind)
    | exact resolve eq26750 eq23193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23193 eq26750
  have eq26755 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq26754 X0
       have j1 := eq26751 X0
       grind)
    | (have r₁ := eq26754 (k (M.op x y) X0)
       have r₂ := eq26751 X0
       grind)
    | (have r₁ := eq26754 X0
       have r₂ := eq26751 X0
       grind)
    | (have r₁ := eq26754 (M.op x y)
       have r₂ := eq26751 (M.op x y)
       grind)
    | exact resolve eq26754 eq26751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26751 eq26754
  have eq26756 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq26755 X0
       have j1 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq26755 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq26755 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26755
  have eq26766 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26344 eq37
    | exact resolve eq37 eq26344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26344
  have eq26773 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq26766
    | exact resolve eq26766 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26766
  have eq27958 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24149 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq24149
    | exact resolve eq24149 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24149
  have eq27998 : ∀ X0 : G, (σ (σ y)) ≠ (σ (σ y)) ∨ (k X0 (σ (σ y))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27958 eq823
    | (have j0 := eq823 (σ y) X0
       grind)
    | exact resolve eq823 eq27958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq28020 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27958 eq18834
    | exact resolve eq18834 eq27958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18834 eq27958
  have eq28024 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28020
  have eq28027 : ∀ X0 : G, (k X0 (σ (σ y))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq27998 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27998
  have eq28059 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28024 eq27
    | exact resolve eq27 eq28024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28024
  have eq28457 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (k (k (M.op x y) X0) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28027 eq49
    | exact resolve eq49 eq28027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq28495 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (k (M.op x y) X0) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24143 eq28457
    | exact resolve eq28457 eq24143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24143 eq28457
  have eq28515 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26756 eq28495
    | exact resolve eq28495 eq26756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26756 eq28495
  have eq28530 : ∀ X0 : G, (k (σ y) (σ X0)) = (k (σ (M.op x y)) (σ (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq28515
    | exact resolve eq28515 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28515
  have eq28538 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26773 eq28530
    | exact resolve eq28530 eq26773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26773 eq28530
  have eq28570 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28538 eq28027
    | exact resolve eq28027 eq28538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28027 eq28538
  have eq28574 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28570
  have eq28586 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28574
       have r₂ := eq28059
       grind)
    | exact resolve eq28574 eq28059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28059 eq28574
  have eq28611 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28586 eq27
    | exact resolve eq27 eq28586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28666 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28586 eq2332
    | exact resolve eq2332 eq28586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2332
  have eq28724 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq28666
    | exact resolve eq28666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28666
  have eq28742 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28586 eq28724
    | exact resolve eq28724 eq28586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28724
  have eq28858 : (σ x) = (k (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28742 eq5394
    | exact resolve eq5394 eq28742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5394
  have eq28887 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28742 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq28742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28903 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28742 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq28742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28938 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq28903
  have eq28959 : (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28586 eq28858
    | exact resolve eq28858 eq28586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28858
  have eq28965 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28586 eq28959
    | exact resolve eq28959 eq28586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28586 eq28959
  have eq37491 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28965 eq2769
    | exact resolve eq2769 eq28965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28965
  have eq37510 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq37491
  have eq37519 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq37510
       have r₂ := eq28611
       grind)
    | exact resolve eq37510 eq28611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37510
  have eq37524 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28742 eq37519
    | exact resolve eq37519 eq28742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28742 eq37519
  have eq37571 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2877 x x
       have i₂ := eq37524
       grind)
    | exact superpose eq37524 eq2877
    | (have r₁ := eq2877 x x
       have r₂ := eq37524
       grind)
    | exact resolve eq2877 eq37524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37524
  have eq37614 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq37571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37571
  have eq37883 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq37614 x
       grind)
    | exact superpose eq37614 eq35
    | exact resolve eq35 eq37614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37614
  have eq37905 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37883
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37883
    | exact resolve eq37883 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37883
  have eq37916 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq28887 (σ x)
       grind)
    | (have r₁ := eq37905
       have r₂ := eq28887 x
       grind)
    | exact resolve eq37905 eq28887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28887 eq37905
  have eq37929 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37916 eq28938
    | exact resolve eq28938 eq37916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28938
  have eq37947 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq37929
  have eq37955 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37947 eq31
    | exact resolve eq31 eq37947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38022 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37947 eq2769
    | exact resolve eq2769 eq37947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769 eq37947
  have eq38214 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq38022
  have eq38247 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq37916 eq38214
    | exact resolve eq38214 eq37916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37916 eq38214
  have eq38295 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq37955
    | exact resolve eq37955 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37955
  have eq38306 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq38247
       have r₂ := eq28611
       grind)
    | exact resolve eq38247 eq28611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28611 eq38247
  have eq39313 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1733 x
       have i₂ := eq38306
       grind)
    | exact superpose eq38306 eq1733
    | exact resolve eq1733 eq38306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733
  have eq39395 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39313
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39313
    | exact resolve eq39313 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39313
  have eq39403 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38295 eq39395
    | exact resolve eq39395 eq38295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38295 eq39395
  have eq39842 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39403 eq9352
    | exact resolve eq9352 eq39403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39403
  have eq40377 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38306
       have i₂ := eq39842
       grind)
    | exact superpose eq39842 eq38306
    | exact resolve eq38306 eq39842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38306 eq39842
  have eq40470 : x = (M.op x y) := by grind
  clear eq40377
  have eq40485 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq40470
       grind)
    | exact superpose eq40470 eq18
    | exact resolve eq18 eq40470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq40486 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq40470
       grind)
    | exact superpose eq40470 eq22
    | exact resolve eq22 eq40470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq40488 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq40470
       grind)
    | exact superpose eq40470 eq39
    | exact resolve eq39 eq40470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq40535 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4088 X0
       have i₂ := eq40470
       grind)
    | exact superpose eq40470 eq4088
    | exact resolve eq4088 eq40470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4088
  have eq40548 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq40486 eq20
    | exact resolve eq20 eq40486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40713 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq40485 eq2231
    | exact resolve eq2231 eq40485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231 eq40485
  have eq40804 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40713 eq3989
    | exact resolve eq3989 eq40713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989
  have eq40810 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40713 eq4136
    | exact resolve eq4136 eq40713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq40848 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq40713 eq2877
    | exact resolve eq2877 eq40713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2877
  have eq40853 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40713 eq11
    | exact resolve eq11 eq40713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40890 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq40853
  have eq40897 : (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40804
       have i₂ := eq40470
       grind)
    | exact superpose eq40470 eq40804
    | exact resolve eq40804 eq40470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40804
  have eq40899 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq40897
       have i₂ := eq40470
       grind)
    | exact superpose eq40470 eq40897
    | exact resolve eq40897 eq40470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40897
  have eq40900 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40713 eq40899
    | exact resolve eq40899 eq40713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40899
  have eq42721 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq40810
       grind)
    | exact superpose eq40810 eq40
    | exact resolve eq40 eq40810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq40810
  have eq42735 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42721
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42721
    | exact resolve eq42721 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42721
  have eq42738 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq42735
    | exact resolve eq42735 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42735
  have eq42741 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40548 eq42738
    | exact resolve eq42738 eq40548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42738
  have eq44265 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40890 eq37
    | exact resolve eq37 eq40890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44288 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq44265
    | exact resolve eq44265 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44265
  have eq44292 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40548 eq44288
    | exact resolve eq44288 eq40548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44288
  have eq44296 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44292
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44292
    | exact resolve eq44292 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44292
  have eq44303 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40900 eq36
    | exact resolve eq36 eq40900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq40900
  have eq44313 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq44303
    | exact resolve eq44303 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44303
  have eq44315 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40548 eq44313
    | exact resolve eq44313 eq40548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44313
  have eq44328 : (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42741 eq15741
    | exact resolve eq15741 eq42741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15741
  have eq44329 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42741 eq16075
    | exact resolve eq16075 eq42741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16075 eq42741
  have eq44356 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (k y y) := by
    first
    | (have j1 := eq40848 y
       grind)
    | (have r₁ := eq44329
       have r₂ := eq40848 x
       grind)
    | exact resolve eq44329 eq40848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40848 eq44329
  have eq44360 : (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | exact superpose eq40548 eq44356
    | exact resolve eq44356 eq40548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44356
  have eq44364 : (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq44296 eq44360
    | exact resolve eq44360 eq44296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44296 eq44360
  have eq45992 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq40535 eq9352
    | exact resolve eq9352 eq40535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40535
  have eq46102 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 X0) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq45992 X0
       grind)
    | (have i₁ := eq11 X0 (M.op x y)
       have i₂ := eq45992 X0
       grind)
    | exact superpose eq45992 eq11
    | exact resolve eq11 eq45992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46476 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ (M.op X0 X0) = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq45992 X0
       grind)
    | exact superpose eq45992 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq45992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46477 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq45992 X0
       grind)
    | exact superpose eq45992 eq12
    | (have j0 := eq12 X0 (M.op x y)
       grind)
    | exact resolve eq12 eq45992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46515 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 X0) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46102 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46102
  have eq46521 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 X0) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq40713 eq46477
    | (have j0 := eq46477 X0
       grind)
    | exact resolve eq46477 eq40713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46477
  have eq46522 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40713 eq46476
    | (have j0 := eq46476 X0
       grind)
    | exact resolve eq46476 eq40713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40713 eq46476
  have eq46536 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq46522 X0
       have j1 := eq46521 X0
       grind)
    | (have r₁ := eq46522 X0
       have r₂ := eq46521 X0
       grind)
    | exact resolve eq46522 eq46521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46521 eq46522
  have eq55979 : ∀ X0 : G, (k (M.op X0 X0) (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9352 X0 X0
       have i₂ := eq46536 (M.op X0 X0)
       grind)
    | exact superpose eq46536 eq9352
    | exact resolve eq9352 eq46536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9352
  have eq56386 : ∀ X0 : G, (k (k X0 (M.op x y)) (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq46536 eq55979
    | exact resolve eq55979 eq46536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46536 eq55979
  have eq57811 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq56386 eq344
    | exact resolve eq344 eq56386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq56386
  have eq57829 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq57811
    | (have j0 := eq57811 X0
       grind)
    | exact resolve eq57811 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57811
  have eq57837 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40548 eq57829
    | exact resolve eq57829 eq40548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57829
  have eq57839 : ∀ X0 : G, (k (k X0 (σ x)) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq57837 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq57837
    | exact resolve eq57837 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57837
  have eq58012 : (τ (σ y)) = (k x x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq44364 eq97
    | exact resolve eq97 eq44364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq44364
  have eq58045 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq58012
       have i₂ := eq40470
       grind)
    | exact superpose eq40470 eq58012
    | exact resolve eq58012 eq40470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58012
  have eq58050 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31 eq58045
    | exact resolve eq58045 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58045
  have eq58277 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq58050
  have eq58290 : y = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq58277
       have r₂ := eq40890
       grind)
    | exact resolve eq58277 eq40890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40890 eq58277
  have eq58319 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq58290 eq40488
    | exact resolve eq40488 eq58290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40488 eq58290
  have eq58337 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq58319
    | exact resolve eq58319 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq58319
  have eq58343 : (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq40548 eq58337
    | exact resolve eq58337 eq40548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58337
  have eq58349 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq58343
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58343
    | exact resolve eq58343 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58343
  have eq58366 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq58349 eq5391
    | exact resolve eq5391 eq58349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5391
  have eq58398 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq58366
       have i₂ := eq45992 sF2
       grind)
    | exact superpose eq45992 eq58366
    | exact resolve eq58366 eq45992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58366
  have eq59106 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq58398 eq17078
    | exact resolve eq17078 eq58398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17078 eq58398
  have eq59170 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (σ y)) ∨ (σ x) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq59106
       have i₂ := eq45992 sF2
       grind)
    | exact superpose eq45992 eq59106
    | exact resolve eq59106 eq45992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59106
  have eq59183 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq46515 eq59170
    | (have j1 := eq46515 (σ x)
       grind)
    | exact resolve eq59170 eq46515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46515 eq59170
  have eq59188 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq58349 eq59183
    | exact resolve eq59183 eq58349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58349 eq59183
  have eq59193 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq59188
       have i₂ := eq45992 sF3
       grind)
    | exact superpose eq45992 eq59188
    | exact resolve eq59188 eq45992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59188
  have eq73639 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44328 eq57839
    | exact resolve eq57839 eq44328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44328 eq57839
  have eq73643 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq73639
  have eq73647 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq44315 eq73643
    | exact resolve eq73643 eq44315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44315 eq73643
  have eq73661 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq73647 eq27
    | exact resolve eq27 eq73647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73647
  have eq73914 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq73661
       have r₂ := eq40548
       grind)
    | exact resolve eq73661 eq40548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73661
  have eq74044 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73914 eq31
    | exact resolve eq31 eq73914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq73914
  have eq74378 : x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq74044
    | exact resolve eq74044 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq74044
  have eq74427 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74378
       have i₂ := eq40470
       grind)
    | exact superpose eq40470 eq74378
    | exact resolve eq74378 eq40470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40470 eq74378
  have eq74428 : y = (M.op x y) := by grind
  clear eq74427
  have eq74469 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq74428
       grind)
    | exact superpose eq74428 eq24
    | exact resolve eq24 eq74428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq74428
  have eq74668 : (σ x) = (σ y) := by
    first
    | exact superpose eq40486 eq74469
    | exact resolve eq74469 eq40486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40486 eq74469
  have eq74669 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq74668 eq26
    | exact resolve eq26 eq74668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq74882 : (σ x) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq74668 eq59193
    | exact resolve eq59193 eq74668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59193 eq74668
  have eq74897 : (σ x) = (M.op (M.op x y) (σ x)) := by grind
  clear eq74882
  have eq74961 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq74669
       have i₂ := eq45992 sF2
       grind)
    | exact superpose eq45992 eq74669
    | exact resolve eq74669 eq45992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45992 eq74669
  have eq74993 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74897 eq74961
    | exact resolve eq74961 eq74897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74897 eq74961
  have eq75026 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq74993 eq27
    | exact resolve eq27 eq74993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq74993
  have eq75299 : False := by grind
  exact eq75299
